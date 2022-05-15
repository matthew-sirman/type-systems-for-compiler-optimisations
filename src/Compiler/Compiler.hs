{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecursiveDo #-}
module Compiler.Compiler where

-- The Compiler mapping functional STFL-Core code into imperative STFL-IR

import qualified Parser.AST as AST (MultiplicityAtom(..), Identifier(..), Literal(..))
import qualified Typing.Types as T
import qualified Util.ConstrainedPoset as P
import qualified Util.Stream as Stream

import Compiler.Translate as Tr

import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Program as IR
import qualified IR.DataType as IR
import IR.InstructionBuilder

import qualified Builtin.Codegen as B

import Prelude hiding (read)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Sequence as Seq hiding (zip, zipWith, unzip, filter, length, take, reverse)
import Data.Bifunctor (bimap)
import Data.Maybe (catMaybes, fromMaybe, fromJust, isJust)
import Data.Word
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
import Data.Array

import Control.Monad.State
import qualified Control.Monad.RevState as Rev
import Control.Monad.Reader
import Control.Monad.Cont
import Control.Applicative
import Control.Lens hiding (Strict, Lazy)

import GHC.Generics
import Data.Hashable (Hashable(..))

-- TODO: Remove
import Typing.Checker
import Parser.Parser
import Debug.Trace
import qualified Builtin.Builtin

type Value = IR.Value Variable
type Instruction = IR.Instruction Variable ReturnStatus
type PhiNode = IR.PhiNode Variable
type BasicBlock = IR.BasicBlock Variable ReturnStatus
type Function = IR.Function Variable ReturnStatus
type Program = IR.Program Variable ReturnStatus

type NameMap = M.HashMap Integer Value

data Variable
    = Variable Evaluation Integer
    | Argument Evaluation Integer
    deriving (Eq, Generic)

instance Show Variable where
    show (Variable _ var) = "%tmp" ++ show var
    show (Argument _ arg) = "%arg" ++ show arg

instance Hashable Variable where
    hashWithSalt salt (Variable _ var) = hashWithSalt salt var
    hashWithSalt salt (Argument _ var) = hashWithSalt salt var
    hash (Variable _ var) = hash var
    hash (Argument _ var) = hash var

data Symbol
    = TypeSymbol String
    | ConsSymbol String
    deriving (Eq, Generic)

instance Hashable Symbol

data ReturnStatus
    = Success
    | Undefined
    | EmptyArgStack
    | EmptySaveStack
    | PatternMatchFail
    | StaticAllocationDependence
    | StaticAllocationFailure
    | HeapAllocationFailure
    | Unknown

instance Show ReturnStatus where
    show Success = "success"
    show Undefined = "undefined"
    show EmptyArgStack = "empty argument stack"
    show EmptySaveStack = "empty save stack"
    show PatternMatchFail = "pattern match failure"
    show StaticAllocationDependence = "attempted to allocate global static block depending on a variable"
    show StaticAllocationFailure = "failed to allocate static memory block"
    show HeapAllocationFailure = "failed to allocate heap memory block"
    show Unknown = "unknown"

data ConsInfo = ConsInfo
    { _consDataType :: IR.DataType
    , _consFunction :: Value
    , _altTag :: Maybe Int
    , _typeName :: String
    }

makeLenses ''ConsInfo

data DataTypeInfo = DataTypeInfo
    { _baseType :: IR.Struct
    , _alternatives :: Array Int ConsInfo
    , _destructor :: Value
    , _isSum :: Bool
    }

makeLenses ''DataTypeInfo

newtype Compiler a = Compiler 
    { runCompiler :: ReaderT CompilerInfo (State CompileState) a
    }
    deriving (Functor, Applicative, Monad, MonadFix, MonadReader CompilerInfo, MonadState CompileState)

data CompileState = CompileState
    { _blockStack :: [BasicBlock]
    , _funcStack :: [Function]
    , _compiledProgram :: Program
    , _dataConsInfo :: M.HashMap AST.Identifier ConsInfo
    , _dataTypeInfo :: M.HashMap String DataTypeInfo
    , _dataPrintFunctions :: M.HashMap String Value
    , _symbolRefs :: M.HashMap Symbol String
    , _labelIDs :: Stream.Stream Int
    , _functionNames :: Stream.Stream IR.FunctionID
    , _thunkNames :: Stream.Stream IR.FunctionID
    , _blockNames :: Stream.Stream IR.Label
    , _variableID :: Integer
    , _thunkReadInfoTable :: Value
    , _defaultDestructor :: Value
    , _builtThunks :: M.HashMap String (IR.DataType, IR.DataType, Value -> [(Bool, Var)] -> Compiler ())
    }

newtype CompilerInfo = CompilerInfo
    { _nameMap :: NameMap
    }

makeLenses ''CompileState
makeLenses ''CompilerInfo

instance MonadIRBuilder Variable ReturnStatus Compiler where
    addInstruction i = modify (blockStack . ix 0 . IR.iList %~ (:|> i))
    throwUndefined = throw Undefined

data BindAlloc
    = Thunk Value Value IR.DataType
    | BoxBind Value
    | ReuseBind (Compiler ())

thunkStruct :: IR.Struct
thunkStruct = IR.Struct "thunk" ["T"] [ infoTableType (IR.TemplateArg "T")
                                      ] False

wrapThunk :: IR.DataType -> IR.DataType
wrapThunk dt = IR.Pointer (IR.NamedStruct thunkStruct [dt])

isThunkType :: IR.DataType -> Bool
isThunkType (IR.Pointer (IR.NamedStruct s _)) = s == thunkStruct
isThunkType (IR.Pointer dt) = isThunkType dt
isThunkType _ = False

infoTableType :: IR.DataType -> IR.DataType
infoTableType baseType = IR.Pointer (IR.Structure [thunkFunc, thunkFunc, thunkFunc, thunkFunc])
    where
        thunkFunc :: IR.DataType
        thunkFunc = IR.FunctionT baseType [IR.VoidPtr]

tagType :: IR.Struct
tagType = IR.Alias "tag" [] IR.I64

reclaimFunction :: IR.DataType -> IR.DataType
reclaimFunction dt = IR.FunctionT IR.Void [dt]

compile :: T.StaticContext -> T.MultiplicityPoset -> CodegenExpr -> Program
compile staticContext poset expr =
    execState (runReaderT (runCompiler createProgram) startInfo) startState ^. compiledProgram
    where
        createProgram :: Compiler ()
        createProgram = do
            createDataTypes
            createThunkFunctions
            pushFunction "main" IR.Void []
            pushBlock
            programResult <- codegen expr
            printResult programResult
            ret Nothing
            popBlock
            void popFunction

        codegen :: CodegenExpr -> Compiler Value
        codegen (Let bindings body) = do
            (allocVarMap, objects) <- unzip <$> mapM allocateThunk bindings
            local (nameMap %~ M.union (M.fromList allocVarMap)) $ do
                zipWithM_ genBinding bindings objects
                codegen body
            where
                allocateThunk :: Binding -> Compiler ((Integer, Value), BindAlloc)
                allocateThunk (LazyBinding _ var (Lf update captures _ _)) = do
                    captureTypes <- mapM lookupCaptureType captures
                    baseType <- strictIRData M.empty (varType var)
                    let extraData = case update of
                                      Updatable -> baseType : captureTypes
                                      _ -> captureTypes
                        thunkType = IR.Structure ( infoTableType baseType
                                                 : extraData
                                                 )
                    thunkVar <- malloc (mkVar Strict) thunkType
                    thunkObject <- bitcast (mkVar Lazy) thunkVar (wrapThunk baseType)
                    pure ((varID (baseVar var), thunkObject), Thunk thunkVar thunkObject baseType)
                allocateThunk (BoxBinding _ var base) = do
                    baseType <- lookupCaptureType (False, base)
                    let thunkType = IR.Structure [ infoTableType baseType
                                                 , baseType
                                                 ]
                    thunkVar <- malloc (mkVar Strict) thunkType
                    thunkObject <- bitcast (mkVar Lazy) thunkVar (wrapThunk baseType)
                    pure ((varID var, thunkObject), Thunk thunkVar thunkObject baseType)
                allocateThunk (Reuse var name _ captures) = do
                    (thunkType, objectType, build) <- gets ((M.! name) . (^. builtThunks))
                    comment "reuse thunk"
                    thunkVar <- malloc (mkVar Strict) thunkType
                    thunkObject <- bitcast (mkVar Lazy) thunkVar objectType
                    pure ((varID var, thunkObject), ReuseBind (build thunkVar captures))

                genBinding :: Binding -> BindAlloc -> Compiler ()
                genBinding (LazyBinding name var (Lf update captures args body)) (Thunk thunkVar thunkObject baseType) = do
                    linearThunk <- sequence $ genThunk ("_@linear_" ++ name) args <$> (body ^. linearBody)
                    relevantThunk <- sequence $ genThunk ("_@relevant_" ++ name) args <$> (body ^. relevantBody)
                    affineThunk <- sequence $ genThunk ("_@affine_" ++ name) (lazyArgs args) <$> (body ^. affineBody)
                    normalThunk <- sequence $ genThunk ("_@normal_" ++ name) (lazyArgs args) <$> (body ^. normalBody)

                    let select = fromMaybe (IR.ValImmediate IR.Undef)

                    infoTable <- createInfoTable name (select (linearThunk <|> relevantThunk <|> affineThunk <|> normalThunk))
                                                      (select (relevantThunk <|> normalThunk))
                                                      (select (affineThunk <|> normalThunk))
                                                      (select normalThunk)
                    let buildThunk thunk caps = do
                            infoPtr <- getElementPtr (mkVar Strict) thunk [0]
                            write infoTable infoPtr
                            zipWithM_ (writeCapture thunk) caps [captureOffset..]

                    buildThunk thunkVar captures
                    let IR.Pointer thunkVarAllocType = IR.datatype thunkVar
                    modify (builtThunks %~ M.insert name (thunkVarAllocType, IR.datatype thunkObject, buildThunk))

                    where
                        genThunk :: String -> [(Bool, TypedVar)] -> CodegenExpr -> Compiler Value
                        genThunk name args body = do
                            argReg <- mkArg Lazy
                            let arg = IR.ValVariable (IR.datatype thunkObject) argReg

                            ---- THUNK ----
                            thunkVal <- pushFunction name baseType [(argReg, IR.datatype thunkObject)]
                            pushBlock

                            -- Pop arguments off the stack
                            argVars <- M.fromList <$> popArgs args

                            argCast <- bitcast (mkVar Strict) arg (IR.datatype thunkVar)
                            closureVars <- M.fromList <$> zipWithM (readCapture argCast) captures [captureOffset..]

                            thunkResult <- local ( (nameMap %~ M.union closureVars)
                                                 . (nameMap %~ M.union argVars)
                                                 . (nameMap %~ M.insert (varID (baseVar var)) arg)
                                                 ) $ codegen body

                            case update of
                              Updatable -> do
                                  -- Get the thunk read function
                                  readTable <- gets (^. thunkReadInfoTable)

                                  infoPtr <- getElementPtr (mkVar Strict) argCast [0]
                                  write readTable infoPtr

                                  resPtr <- getElementPtr (mkVar Strict) argCast [1]
                                  write thunkResult resPtr
                              FreeAfterUse -> do
                                  free arg
                              NonUpdatable -> pure ()

                            ret (Just thunkResult)
                            popBlock
                            popFunction

                            pure thunkVal

                        captureOffset :: Int
                        captureOffset = case update of
                                          Updatable -> 2
                                          _ -> 1

                        popArgs :: [(Bool, TypedVar)] -> Compiler [(Integer, Value)]
                        popArgs [] = pure []
                        popArgs ((strict, arg):args) = do
                            rest <- popArgs args
                            dt <- if strict then strictIRData M.empty (varType arg) else lazyIRData M.empty (varType arg)
                            val <- pop (mkVar (if strict then Strict else Lazy)) dt
                            pure ((varID (baseVar arg), val) : rest)
                genBinding (BoxBinding _ var source) (Thunk thunkVar _ _) = do
                    readTable <- gets (^. thunkReadInfoTable)

                    infoPtr <- getElementPtr (mkVar Strict) thunkVar [0]
                    write readTable infoPtr

                    thunkData <- lookupVar source
                    resPtr <- getElementPtr (mkVar Strict) thunkVar [1]
                    write thunkData resPtr 
                genBinding (Reuse {}) (ReuseBind buildBinding) = buildBinding
                genBinding _ _ = comment "ERROR: mismatched binding generation."

                lazyArgs :: [(Bool, TypedVar)] -> [(Bool, TypedVar)]
                lazyArgs = map (\(_, v) -> (False, v))

                writeCapture :: Value -> (Bool, Var) -> Int -> Compiler ()
                writeCapture base (strict, v) offset = do
                    capVal <- lookupVar v
                    wrapped <- wrapStrict capVal
                    capPtr <- getElementPtr (mkVar Strict) base [offset]
                    write wrapped capPtr
                    where
                        wrapStrict :: Value -> Compiler Value
                        wrapStrict val
                            | not (isThunkType (IR.datatype val)) = do
                                readTable <- gets (^. thunkReadInfoTable)

                                let thunkType = IR.Structure [ IR.datatype readTable
                                                             , IR.datatype val
                                                             ]
                                thunkShell <- malloc (mkVar Strict) thunkType
                                infoPtr <- getElementPtr (mkVar Strict) thunkShell [0]
                                write readTable infoPtr

                                resPtr <- getElementPtr (mkVar Strict) thunkShell [1]
                                write val resPtr

                                bitcast (mkVar Lazy) thunkShell (wrapThunk (IR.datatype val))
                            | otherwise = pure val

                readCapture :: Value -> (Bool, Var) -> Int -> Compiler (Integer, Value)
                readCapture base (_, v) offset = do
                    addr <- getElementPtr (mkVar Strict) base [offset]
                    val <- read (mkVar Lazy) addr
                    pure (varID v, val)

                lookupCaptureType :: (Bool, Var) -> Compiler IR.DataType
                lookupCaptureType (strict, v) = do
                    val <- asks (M.lookup (varID v) . (^. nameMap))
                    let wrap dt = if isThunkType dt
                                     then dt
                                     else wrapThunk dt
                    pure (maybe (wrapThunk IR.VoidPtr) (wrap . IR.datatype) val)

        codegen (Case disc branches) = do
            discVal <- codegen disc
            -- Entry:
            --  ... | entry
            -- Push rest block:
            --  ... | entry | rest
            pushBlock
            restLabel <- blockLabel
            -- Swap:
            --  ... | rest | entry
            swapBlocks
            -- Generate branches:
            --  ... | rest | exit
            phiNodes <- genBranches restLabel discVal (toList branches)
            -- Pop exit node:
            --  ... | rest
            popBlock
            phi (mkVar Strict) phiNodes
            where
                genBranches :: IR.Label -> Value -> [Tr.Alternative] -> Compiler [PhiNode]
                genBranches _ _ [] = do
                    throw PatternMatchFail
                    pure []
                genBranches successLabel var (Alt dealloc pattern expr:rest) = do
                    branchCanFail <- canFail pattern
                    -- Entry:
                    --  ... | entry
                    -- Push fail block:
                    --  ... | entry | fail
                    pushBlock
                    failLabel <- blockLabel
                    -- Swap:
                    --  ... | fail | entry
                    swapBlocks
                    -- Generate branch:
                    --  ... | fail | exit
                    names <- unpackPattern dealloc failLabel pattern var
                    branchVal <- local (nameMap %~ M.union names) $ codegen expr
                    jump successLabel
                    branchLabel <- blockLabel
                    -- Pop block:
                    --  ... | fail
                    popBlock
                    nodes <- if branchCanFail
                                then genBranches successLabel var rest
                                else pure []
                    pure (IR.PhiNode (branchVal, branchLabel) : nodes)

                canFail :: Pattern -> Compiler Bool
                canFail (VarPattern _) = pure False
                canFail (LitPattern _) = pure True
                canFail (ConsPattern cons ps) = do
                    consInfo <- gets ((M.! cons) . (^. dataConsInfo))
                    case consInfo ^. altTag of
                      Just _ -> pure True
                      Nothing -> or <$> mapM canFail ps
                canFail (TuplePattern ps) = or <$> mapM canFail ps

        codegen (Application resType mul fun args) = do
            funVal <- lookupVar fun
            forM_ args $ \case
                Var v -> lookupVar v >>= push
                Lit l -> genLiteral l >>= push
            result <- forceCompute mul funVal
            bitcast (mkVar Strict) result =<< strictIRData M.empty resType

        codegen (PrimApp affine fun args) = do
            argVals <- forM args $ \case
                -- True because primitives are always strict in their args
                Var v -> lookupVar v >>= forceCompute (True, affine)
                Lit l -> genLiteral l
            B.generatePrimitive (mkVar Strict) fun argVals

        codegen (ConsApp affine consId@(AST.I cons) args) = do
            consInfo <- gets ((M.! consId) . (^. dataConsInfo))
            argVals <- forM args $ \case
                Var v -> lookupVar v
                Lit l -> genLiteral l
            consVal <- call (mkVar Strict) (consInfo ^. consFunction) argVals
            reclaim <- if affine
                          then gets ((^. destructor) . (M.! (consInfo ^. typeName)) . (^. dataTypeInfo))
                          else gets (^. defaultDestructor)
            reclaimPtr <- bitcast (mkVar Strict) consVal (IR.Pointer (IR.datatype reclaim))
            write reclaim reclaimPtr
            pure consVal

        codegen (PackedTuple vs) = do
            elemTypes <- mapM argType vs
            tuplePtr <- malloc (mkVar Strict) (IR.Structure elemTypes)
            zipWithM_ (writeVal tuplePtr) vs [0..]
            pure tuplePtr
            where
                argType :: Atom -> Compiler IR.DataType
                argType (Var v) = IR.datatype <$> lookupVar v
                argType (Lit (T.IntLit _)) = pure (IR.FirstOrder IR.Int64T)
                argType (Lit (T.RealLit _)) = pure (IR.FirstOrder IR.Real64T)

                getValue :: Atom -> Compiler Value
                getValue (Var v) = lookupVar v
                getValue (Lit l) = genLiteral l

                writeVal :: Value -> Atom -> Int -> Compiler ()
                writeVal base atom offset = do
                    elemPtr <- getElementPtr (mkVar Strict) base [offset]
                    val <- getValue atom
                    write val elemPtr

        codegen (Projector mul offset v) = do
            base <- lookupVar v
            forced <- forceCompute mul base
            addr <- getElementPtr (mkVar Strict) forced [offset]
            value <- read (mkVar Lazy) addr
            forceCompute mul value

        codegen Error = do
            throw Unknown
            pure (IR.ValImmediate IR.Undef)

        lookupVar :: Var -> Compiler Value
        lookupVar v = do
            maybeVar <- asks (M.lookup (varID v) . (^. nameMap))
            case maybeVar of
              Just var -> pure var
              Nothing -> error (show v)

        genLiteral :: T.PrimitiveLiteral -> Compiler Value
        genLiteral (T.IntLit i) = pure (mkInt i)
        genLiteral (T.RealLit r) = pure (IR.ValImmediate (IR.Real64 r))

        forceCompute :: (Bool, Bool) -> Value -> Compiler Value
        forceCompute mul val
            | evaluation val == Lazy = do
                infoPtr <- getElementPtr (mkVar Strict) val [0]
                infoTable <- read (mkVar Strict) infoPtr
                funPtr <- getElementPtr (mkVar Strict) infoTable [entryOffset mul]
                function <- read (mkVar Strict) funPtr
                call (mkVar Strict) function [val]
            | otherwise = pure val
            where
                entryOffset :: (Bool, Bool) -> Int
                entryOffset (True, True) = 0
                entryOffset (True, False) = 1
                entryOffset (False, True) = 2
                entryOffset (False, False) = 3

        unpackPattern :: Bool -> IR.Label -> Pattern -> Value -> Compiler NameMap
        unpackPattern dealloc failLabel pattern v = do
            unpack pattern v
            where
                unpack :: Pattern -> Value -> Compiler NameMap
                unpack (VarPattern name) var =
                    pure (M.singleton (varID (baseVar name)) var)
                unpack (ConsPattern cons args) var = do
                    forced <- forceCompute (False, dealloc) var
                    consInfo <- gets ((M.! cons) . (^. dataConsInfo))
                    case consInfo ^. altTag of
                      Nothing -> do
                          nameMaps <- zipWithM (unpackElem forced) args [[i] | i <- [1..]]
                          when dealloc $ do
                              destructorPtr <- bitcast (mkVar Strict) forced (IR.Pointer (reclaimFunction (IR.datatype forced)))
                              destructor <- read (mkVar Strict) destructorPtr
                              voidCall destructor [forced]
                          pure (M.unions nameMaps)
                      Just index -> do
                          -- Entry:
                          --  ... | entry
                          -- First, push the "rest" block
                          --  ... | entry | rest
                          pushBlock
                          restLabel <- blockLabel

                          -- Now, swap so entry is on top:
                          --  ... | rest | entry
                          swapBlocks
                          header <- bitcast (mkVar Strict) forced (IR.Pointer (IR.Structure [reclaimFunction IR.VoidPtr, IR.I64]))
                          tagPtr <- getElementPtr (mkVar Strict) header [1]
                          tagVal <- read (mkVar Strict) tagPtr
                          cmp <- binop IR.NotEqual (mkVar Strict) tagVal (mkInt index)
                          branch cmp failLabel
                          -- Pop the entry block
                          --    ... | rest

                          popBlock
                          let branchType = IR.Pointer (consInfo ^. consDataType)
                          branchPtr <- bitcast (mkVar Strict) forced branchType
                          nameMaps <- zipWithM (unpackElem branchPtr) args [[i] | i <- [2..]]
                          when dealloc $ do
                              destructorPtr <- bitcast (mkVar Strict) forced (IR.Pointer (reclaimFunction (IR.datatype forced)))
                              destructor <- read (mkVar Strict) destructorPtr
                              voidCall destructor [forced]
                          pure (M.unions nameMaps)
                unpack (TuplePattern ts) var = do
                    forced <- forceCompute (False, dealloc) var
                    nameMaps <- zipWithM (unpackElem forced) ts [[i] | i <- [0..]]
                    pure (M.unions nameMaps)
                unpack (LitPattern lit) var = do
                    forced <- forceCompute (True, dealloc) var
                    unpackLit forced lit
                    pure M.empty
                    where
                        unpackLit :: Value -> T.PrimitiveLiteral -> Compiler ()
                        unpackLit forced (T.IntLit i) = literalMatcher forced (mkInt i)
                        unpackLit forced (T.RealLit r) = literalMatcher forced (IR.ValImmediate (IR.Real64 r))

                        literalMatcher :: Value -> Value -> Compiler ()
                        literalMatcher forced checkValue = do
                            cmp <- binop IR.NotEqual (mkVar Strict) forced checkValue
                            branch cmp failLabel
                            popBlock
                            pushBlock
                
                unpackElem :: Value -> Pattern -> [Int] -> Compiler NameMap
                unpackElem forced pat index = do
                    elemPtr <- getElementPtr (mkVar Strict) forced index
                    let elemEval
                            | isThunkType (IR.datatype elemPtr) = Lazy
                            | otherwise = Strict
                    elem <- read (mkVar elemEval) elemPtr
                    unpack pat elem

        pushFunction :: String -> IR.DataType -> [(Variable, IR.DataType)]
                     -> Compiler Value
        pushFunction name retType args = do
            let func = IR.makeFunc (IR.FID name) retType args
            modify (funcStack %~ (func:))
            pure (IR.functionValue func)

        popFunction :: Compiler Function
        popFunction = do
            (fn, rest) <- gets (uncons . (^. funcStack))
            modify (funcStack .~ rest)
            modify (compiledProgram %~ IR.addFunction fn)
            pure fn
            where
                uncons :: [a] -> (a, [a])
                uncons (x:xs) = (x, xs)
                uncons _ = error "Uncons failed"

        pushBlock :: Compiler ()
        pushBlock = do
            blockId <- popName blockNames
            let block = IR.makeBasicBlock blockId
            modify (blockStack %~ (block:))

        popBlock :: Compiler ()
        popBlock = do
            (blk, rest) <- gets (uncons . (^. blockStack))
            modify ( (blockStack .~ rest)
                   . (funcStack . ix 0 . IR.blocks %~ (:|> blk))
                   )
            where
                uncons :: [a] -> (a, [a])
                uncons (x:xs) = (x, xs)
                uncons _ = error "Uncons failed"

        swapBlocks :: Compiler ()
        swapBlocks = do
            blks <- gets (^. blockStack)
            case blks of
              (b0:b1:rest) -> modify (blockStack .~ b1:b0:rest)
              _ -> pure ()

        blockLabel :: Compiler IR.Label
        blockLabel = gets (^. blockStack . ix 0 . IR.label)

        popName :: Lens' CompileState (Stream.Stream a) -> Compiler a
        popName stream = do
            (name Stream.:> rest) <- gets (^. stream)
            modify (stream .~ rest)
            pure name

        newVar :: Compiler Integer
        newVar = do
            v <- gets (^. variableID)
            modify (variableID %~ (+1))
            pure v

        mkVar :: Evaluation -> Compiler Variable
        mkVar eval = Variable eval <$> newVar

        mkArg :: Evaluation -> Compiler Variable
        mkArg eval = Argument eval <$> newVar

        mkInt :: Integral a => a -> Value
        mkInt = IR.ValImmediate . IR.Int64 . fromIntegral

        mkInt1 :: Bool -> Value
        mkInt1 = IR.ValImmediate . IR.Int1 

        strictIRData :: M.HashMap PolyVar IR.DataType -> TranslateType -> Compiler IR.DataType
        strictIRData _ IntT = pure IR.I64
        strictIRData _ RealT = pure IR.R64
        strictIRData pmap (Poly p) = pure IR.VoidPtr
            -- case M.lookup p pmap of
            --   Just t -> pure t
            --   Nothing -> pure IR.VoidPtr
        -- NOTE: Using lazyIRData here might break things
        strictIRData pmap (Tuple ts) = IR.Pointer . IR.Structure <$> mapM (lazyIRData pmap) ts
        strictIRData _ (Named (AST.I name)) = do
            val <- gets (M.lookup name . (^. dataTypeInfo))
            case val of
              Just v -> pure (IR.Pointer (IR.NamedStruct (v ^. baseType) []))
              Nothing -> pure IR.VoidPtr
        strictIRData pmap (Function ret _) = strictIRData pmap ret
            -- ret' <- strictIRData pmap ret
            -- let func = IR.FunctionT ret' [voidPtr]
            -- pure (IR.Pointer (IR.Structure [func, func]))
        strictIRData pmap (TypeApp (AST.I name) args) = do
            val <- gets (M.lookup name . (^. dataTypeInfo))
            argDataTypes <- mapM (strictIRData pmap) args
            case val of
              Just v -> pure (IR.Pointer (IR.NamedStruct (v ^. baseType) argDataTypes))
              Nothing -> error (show name)

        lazyIRData :: M.HashMap PolyVar IR.DataType -> TranslateType -> Compiler IR.DataType
        lazyIRData _ IntT = pure IR.I64
        lazyIRData _ RealT = pure IR.R64
        -- lazyIRData pmap (Tuple ts) = wrapThunk . IR.Pointer . IR.Structure <$> mapM (lazyIRData pmap) ts
        lazyIRData pmap t = wrapThunk <$> strictIRData pmap t

        createInfoTable :: String -> Value -> Value -> Value -> Value -> Compiler Value
        createInfoTable name linear relevant affine normal = do
            let infoTable = IR.GlobalBlock
                                { IR._globalName = "_info_table_" ++ name
                                , IR._blockData = [linear, relevant, affine, normal]
                                }
            modify (compiledProgram %~ IR.addGlobal infoTable)
            pure (IR.ValGlobal infoTable)

        createDataTypes :: Compiler ()
        createDataTypes = do
            modify (compiledProgram %~ IR.addStruct thunkStruct)
            modify (compiledProgram %~ IR.addStruct tagType)
            let programDataTypes = M.toList (staticContext ^. T.dataTypes)
            mapM_ (\(tn, (tvs, _)) -> forwardDeclType tn tvs) programDataTypes
            structs <- mapM (uncurry createDataType) programDataTypes
            createPrintFunctions structs
        
        forwardDeclType :: AST.Identifier -> S.HashSet T.TypeVar -> Compiler ()
        forwardDeclType (AST.I typeName) tvs = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])
                fdecl = IR.ForwardDecl ("_type_" ++ typeName) typeVars
                info = DataTypeInfo fdecl (listArray (0, -1) []) (IR.ValImmediate IR.Undef) True
            modify (compiledProgram %~ IR.addStruct fdecl)
            modify (dataTypeInfo %~ M.insert typeName info)

        createDataType :: AST.Identifier
                       -> (S.HashSet T.TypeVar, [(AST.Identifier, (T.TypeScheme, [T.Type]))])
                       -> Compiler IR.Struct
        createDataType (AST.I typeName) (tvs, []) = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])

            let union = IR.Union ("_type_" ++ typeName) typeVars []
            modify (compiledProgram %~ IR.addStruct union)
            let info = DataTypeInfo union (listArray (0, -1) []) (IR.ValImmediate IR.Undef) True

            modify (dataTypeInfo %~ M.insert typeName info)
            modify (compiledProgram %~ IR.addStruct union)
            modify (symbolRefs %~ M.insert (TypeSymbol (IR.structBaseName union)) typeName)

            pure union

        createDataType (AST.I typeName) (tvs, [(cons, (_, argTypes))]) = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])
                typeVArgs = map IR.TemplateArg typeVars
                typeVarMap = M.fromList (zip (map PolyVar (S.toList tvs)) typeVars)

            (consStruct, components) <- createDataConstructor False typeName typeVars typeVarMap argTypes cons
            let alias = IR.Alias ("_type_" ++ typeName) typeVars consStruct
                aliasDataType = IR.NamedStruct alias typeVArgs

            consInfo <- createConsFunction typeName aliasDataType (cons, Nothing) (consStruct, components)
            destructor <- createDestructor aliasDataType typeName
            let info = DataTypeInfo alias (listArray (0, 0) [consInfo]) destructor False

            modify (dataTypeInfo %~ M.insert typeName info)
            modify (compiledProgram %~ IR.addStruct alias)
            modify (symbolRefs %~ M.insert (TypeSymbol (IR.structBaseName alias)) typeName)

            pure alias

        createDataType (AST.I typeName) (tvs, conss) = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])
                typeVArgs = map IR.TemplateArg typeVars
                typeVarMap = M.fromList (zip (map PolyVar (S.toList tvs)) typeVars)

            consTypes <- mapM (\(cons, (_, args)) -> createDataConstructor True typeName typeVars typeVarMap args cons) conss
            let union = IR.Union ("_type_" ++ typeName) typeVars (map fst consTypes)
                unionDataType = IR.NamedStruct union typeVArgs

            consInfos <- zipWithM (createConsFunction typeName unionDataType) (zip (map fst conss) (map Just [0..])) consTypes
            destructor <- createDestructor unionDataType typeName
            let info = DataTypeInfo union (listArray (0, length conss - 1) consInfos) destructor True

            modify (dataTypeInfo %~ M.insert typeName info)
            modify (compiledProgram %~ IR.addStruct union)
            modify (symbolRefs %~ M.insert (TypeSymbol (IR.structBaseName union)) typeName)

            pure union

        createDataConstructor :: Bool -> String -> [IR.TemplateArgName] -> M.HashMap PolyVar IR.TemplateArgName
                              -> [T.Type] -> AST.Identifier
                              -> Compiler (IR.DataType, [IR.DataType])
        createDataConstructor tagged typeName tArgs subMap argTypes consId@(AST.I consName) = do
            -- componentDataTypes <- mapM (strictIRData (M.map IR.TemplateArg subMap) . typeToTType poset) argTypes
            componentDataTypes <- mapM findType argTypes
            let consSymbol = "_cons_" ++ typeName ++ "__" ++ consName
                components
                    | tagged = IR.NamedStruct tagType [] : componentDataTypes
                    | otherwise = componentDataTypes
                consDataStruct = IR.Struct consSymbol tArgs (reclaimFunction IR.VoidPtr : components) False

            modify (compiledProgram %~ IR.addStruct consDataStruct)
            modify (symbolRefs %~ M.insert (ConsSymbol consSymbol) consName)
            pure (IR.NamedStruct consDataStruct (map IR.TemplateArg tArgs), componentDataTypes)
            where
                findType :: T.Type -> Compiler IR.DataType
                findType (T.Ground (AST.I "Int#")) = pure IR.I64
                findType (T.Ground (AST.I "Real#")) = pure IR.R64
                findType t = wrapThunk <$> strictIRData (M.map IR.TemplateArg subMap) (typeToTType t)

        createConsFunction :: String -> IR.DataType -> (AST.Identifier, Maybe Int) -> (IR.DataType, [IR.DataType])
                           -> Compiler ConsInfo
        createConsFunction baseTypeName baseDataType (consId@(AST.I consName), altIndex) (consDataType, argTypes) = do
            funcArgs <- mapM (\dt -> (,dt) <$> mkArg Strict) argTypes
            funcVal <- pushFunction ("_cons_" ++ consName) (IR.Pointer baseDataType) funcArgs
            pushBlock

            dataPtr <- malloc (mkVar Strict) baseDataType
            case altIndex of
              Nothing -> zipWithM_ (writeArgElement dataPtr) funcArgs [1..]
              Just index -> do
                  castPtr <- bitcast (mkVar Strict) dataPtr (IR.Pointer consDataType)
                  altTagPtr <- getElementPtr (mkVar Strict) castPtr [1]
                  write (mkInt index) altTagPtr
                  zipWithM_ (writeArgElement castPtr) funcArgs [2..]

            ret (Just dataPtr)

            popBlock
            popFunction

            let info = ConsInfo consDataType funcVal altIndex baseTypeName

            modify (dataConsInfo %~ M.insert consId info)
            pure info
            where
                writeArgElement :: Value -> (Variable, IR.DataType) -> Int -> Compiler ()
                writeArgElement basePtr (var, varType) index = do
                    elemPtr <- getElementPtr (mkVar Strict) basePtr [index]
                    write (IR.ValVariable varType var) elemPtr

        createDestructor :: IR.DataType -> String -> Compiler Value
        createDestructor dt name = do
            funcArg <- mkArg Strict
            destructor <- pushFunction ("_destroy_" ++ name) IR.Void [(funcArg, IR.Pointer dt)]
            pushBlock

            free (IR.ValVariable (IR.Pointer dt) funcArg)

            ret Nothing
            popBlock
            void popFunction

            pure destructor

        createPrintFunctions :: [IR.Struct] -> Compiler ()
        createPrintFunctions [] = pure ()
        createPrintFunctions (struct:structs) = do
            dataArgReg <- mkArg Strict
            let dataArgType = IR.Pointer (IR.NamedStruct struct (map IR.TemplateArg templates))
                dataArg = IR.ValVariable dataArgType dataArgReg
                name = "__print__" ++ IR.structBaseName struct
            printFuncArgRegs <- mapM parametricPrintFunction templates
            let printFuncArgs = M.fromList (zip templates (map (uncurry (flip IR.ValVariable)) printFuncArgRegs))

            printFunction <- pushFunction name IR.Void ((dataArgReg, dataArgType) : printFuncArgRegs)
            name <- gets ((M.! TypeSymbol (IR.structBaseName struct)) . (^. symbolRefs))
            modify (dataPrintFunctions %~ M.insert name printFunction)

            createPrintFunctions structs

            pushBlock
            runReaderT (printNamed struct dataArg) printFuncArgs
            ret Nothing
            popBlock
            void popFunction
            where
                templates :: [IR.TemplateArgName]
                templates = zipWith (\_ i -> "T" ++ show i) (IR.structArgs struct) [0..]

                parametricPrintFunction :: IR.TemplateArgName -> Compiler (Variable, IR.DataType)
                parametricPrintFunction tArg = do
                    argReg <- mkArg Strict
                    pure (argReg, IR.FunctionT IR.Void [IR.TemplateArg tArg])

                printNamed :: IR.Struct -> Value
                           -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()
                printNamed (IR.Struct symbol argNames ts _) val = do
                    typeName <- gets (M.lookup (TypeSymbol symbol) . (^. symbolRefs))
                    consName <- gets (M.lookup (ConsSymbol symbol) . (^. symbolRefs))
                    let name = fromMaybe "<unknown>" (typeName <|> consName)
                    case ts of
                      [] -> error "Badly formed structure"
                      [_] -> named [] 1 name
                      (_ : IR.NamedStruct tag [] : ts)
                        | tag == tagType -> named ts 2 name
                      (_ : ts) -> named ts 1 name
                    where
                        named :: [IR.DataType] -> Int -> String -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()
                        named [] _ name = lift $ printf name []
                        named ts offset name = do
                            lift $ printf ("(" ++ name ++ " ") []
                            intercalatePrintM " " (zipWith (printSubValue val) ts [offset..])
                            lift $ printf ")" []
                printNamed (IR.Union symbol argNames ts) val = do
                    header <- lift $ bitcast (mkVar Strict) val (IR.Pointer (IR.Structure [reclaimFunction IR.VoidPtr, IR.I64]))
                    tagPtr <- lift $ getElementPtr (mkVar Strict) header [1]
                    tag <- lift $ read (mkVar Strict) tagPtr
                    lift pushBlock
                    restLabel <- lift blockLabel
                    lift swapBlocks
                    typeName <- gets (M.lookup (TypeSymbol symbol) . (^. symbolRefs))
                    consName <- gets (M.lookup (ConsSymbol symbol) . (^. symbolRefs))
                    typeInfo <- gets ((M.! fromJust (typeName <|> consName)) . (^. dataTypeInfo))
                    matchTag restLabel tag val (assocs (typeInfo ^. alternatives))
                    lift popBlock
                    where
                        matchTag :: IR.Label -> Value -> Value -> [(Int, ConsInfo)]
                                 -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()
                        matchTag successLabel _ _ [] = lift $ jump successLabel
                        matchTag successLabel tagVal dataPtr ((tag, consInfo):ts) = do
                            -- Entry:
                            --  ... | entry
                            -- Push match block:
                            --  ... | entry | match
                            lift pushBlock
                            matchLabel <- lift blockLabel
                            -- Swap blocks:
                            --  ... | match | entry
                            lift swapBlocks
                            cmp <- lift $ binop IR.Equal (mkVar Strict) tagVal (mkInt tag)
                            lift $ branch cmp matchLabel
                            -- Pop entry:
                            --  ... | match
                            lift popBlock
                            -- Push other branches:
                            --  ... | match | entry'
                            lift pushBlock
                            matchTag successLabel tagVal dataPtr ts
                            -- Pop branch return:
                            --  ... | match
                            lift popBlock
                            -- Display this branch
                            let branchType = IR.Pointer (consInfo ^. consDataType)
                            branchPtr <- lift $ bitcast (mkVar Strict) dataPtr branchType
                            printValue branchType branchPtr
                            lift $ jump successLabel
                printNamed (IR.Alias _ argNames (IR.NamedStruct s args)) val = printNamed s val
                printNamed t _ = error (show t)

                printSubValue :: Value -> IR.DataType -> Int
                              -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()
                printSubValue base dt index = do
                    elemPtr <- lift $ getElementPtr (mkVar Strict) base [index]
                    let eval = if isThunkType dt then Lazy else Strict
                    elem <- lift $ read (mkVar eval) elemPtr
                    forced <- lift $ forceCompute (True, True) elem
                    printValue (IR.datatype forced) forced
                
                printValue :: IR.DataType -> Value
                           -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()
                printValue IR.I64 val = lift $ printf "%d" [val]
                printValue IR.R64 val = lift $ printf "%f" [val]
                printValue IR.Void val = lift $ printf "error" []
                printValue (IR.FirstOrder IR.UnitT) _ = lift $ printf "()" []
                printValue (IR.Pointer (IR.NamedStruct s args)) val = do
                    symbol <- gets (M.lookup (TypeSymbol (IR.structBaseName s)) . (^. symbolRefs))
                    case symbol of
                      Just typeName -> do
                          printFunction <- gets ((M.! typeName) . (^. dataPrintFunctions))
                          parametricArgs <- mapM getParametricPrinter args
                          lift $ voidCall printFunction (val : parametricArgs)
                      _ -> printNamed s val
                printValue (IR.Pointer (IR.Structure ts)) val = do
                    lift $ printf "(" []
                    intercalatePrintM ", " (zipWith (printSubValue val) ts [0..])
                    lift $ printf ")" []
                printValue (IR.FunctionT {}) val = lift $ printf "fun" []
                printValue (IR.Pointer {}) val = lift $ printf "ptr" []
                printValue (IR.TemplateArg arg) val = do
                    printer <- asks (M.! arg)
                    lift $ voidCall printer [val]
                printValue t _ = pure ()

                getParametricPrinter :: IR.DataType
                                     -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler Value
                getParametricPrinter (IR.TemplateArg arg) = asks (M.! arg)
                getParametricPrinter _ = pure (IR.ValVariable (IR.FunctionT IR.Void [IR.VoidPtr]) (Variable Strict (-1)))

                intercalatePrintM :: String -> [ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()]
                                  -> ReaderT (M.HashMap IR.TemplateArgName Value) Compiler ()
                intercalatePrintM _ [] = pure ()
                intercalatePrintM _ [printer] = printer
                intercalatePrintM sep (printer:printers) = do
                    printer
                    lift $ printf sep []
                    intercalatePrintM sep printers

        createThunkFunctions :: Compiler ()
        createThunkFunctions = do
            -- Read function
            readArgReg <- mkArg Strict
            let template = IR.Pointer (IR.TemplateArg "T")
                thunkType = IR.Pointer (IR.Structure [IR.VoidPtr, template])
                readArg = IR.ValVariable thunkType readArgReg
            readThunkFunction <- pushFunction "__read_thunk_value" template [(readArgReg, thunkType)]
            pushBlock
            payloadPtr <- getElementPtr (mkVar Strict) readArg [1]
            payload <- read (mkVar Strict) payloadPtr
            ret (Just payload)
            popBlock
            popFunction

            let infoTable = IR.GlobalBlock
                                { IR._globalName = "_info_table__read_thunk_value"
                                , IR._blockData = [readThunkFunction, readThunkFunction, readThunkFunction, readThunkFunction]
                                }

            modify (compiledProgram %~ IR.addGlobal infoTable)
            modify (thunkReadInfoTable .~ IR.ValGlobal infoTable)

            -- Default destructor
            destructorArg <- mkArg Strict
            destructor <- pushFunction "__no_destructor" IR.Void [(destructorArg, IR.VoidPtr)]
            pushBlock
            ret Nothing
            popBlock
            popFunction

            modify (defaultDestructor .~ destructor)

        printResult :: Value -> Compiler ()
        printResult result = do
            forced <- forceCompute (True, True) result
            case IR.datatype forced of
              IR.Pointer (IR.NamedStruct struct args) -> do
                  typeName <- gets ((M.! TypeSymbol (IR.structBaseName struct)) . (^. symbolRefs))
                  printFunction <- gets ((M.! typeName) . (^. dataPrintFunctions))
                  argFunctions <- mapM getParametricPrinter args
                  voidCall printFunction (forced : argFunctions)
              t -> error (show t)
            printf "\n" []
            where
                getParametricPrinter :: IR.DataType -> Compiler Value
                getParametricPrinter (IR.Pointer (IR.NamedStruct struct [])) = do
                    typeName <- gets ((M.! TypeSymbol (IR.structBaseName struct)) . (^. symbolRefs))
                    gets ((M.! typeName) . (^. dataPrintFunctions))
                getParametricPrinter t = error (show t)

        evaluation :: Value -> Evaluation
        evaluation (IR.ValVariable _ (Variable eval _)) = eval
        evaluation (IR.ValVariable _ (Argument eval _)) = eval
        evaluation _ = Strict

        startState :: CompileState
        startState = CompileState 
            { _blockStack = []
            , _funcStack = []
            , _compiledProgram = IR.emptyProgram
            , _dataConsInfo = M.empty
            , _dataTypeInfo = M.empty
            , _dataPrintFunctions = M.empty
            , _symbolRefs = M.empty
            , _labelIDs = Stream.iterate (+1) 0
            , _functionNames = fmap (\f -> IR.FID ("__anonymous_" ++ show f)) (Stream.iterate (+1) 0)
            , _thunkNames = fmap (\f -> IR.FID ("__thunk_" ++ show f)) (Stream.iterate (+1) 0)
            , _blockNames = fmap (\b -> IR.Label ("block_" ++ show b)) (Stream.iterate (+1) 0)
            , _variableID = 0
            , _thunkReadInfoTable = IR.ValImmediate IR.Undef
            , _defaultDestructor = IR.ValImmediate IR.Undef
            , _builtThunks = M.empty
            }
        
        startInfo :: CompilerInfo
        startInfo = CompilerInfo
            { _nameMap = M.empty
            }

