{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecursiveDo #-}
module Compiler.Compiler where

import qualified Parser.AST as AST (MultiplicityAtom(..), Identifier(..), Literal(..))
import qualified Typing.Types as T
-- import Typing.Types
--     ( Pattern(..)
--     , Type(..)
--     , Multiplicity(..)
--     , Arrow(..)
--     , typeof
--     )
import qualified Util.BoundedPoset as P
import qualified Util.Stream as Stream

import Compiler.Translate

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
import Control.Lens hiding (Strict, Lazy)

import GHC.Generics
import Data.Hashable (Hashable(..))

-- TODO: Remove
import Typing.Checker
import Parser.Parser
import Debug.Trace
import qualified Builtin.Builtin

type Value = IR.Value Variable
type Instruction = IR.Instruction Variable
type PhiNode = IR.PhiNode Variable
type BasicBlock = IR.BasicBlock Variable
type Function = IR.Function Variable
type Program = IR.Program Variable

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

data ConsInfo = ConsInfo
    { _consDataType :: IR.DataType
    , _consFunction :: Value
    , _altTag :: Maybe Int
    }

makeLenses ''ConsInfo

data DataTypeInfo = DataTypeInfo
    { _baseType :: IR.Struct
    , _alternatives :: Array Int ConsInfo
    , _isProduct :: Bool
    }

makeLenses ''DataTypeInfo

data CompileState = CompileState
    { _blockStack :: [BasicBlock]
    , _funcStack :: [Function]
    , _compiledProgram :: Program
    , _dataConsInfo :: M.HashMap AST.Identifier ConsInfo
    , _dataTypeInfo :: M.HashMap String DataTypeInfo
    , _symbolRefs :: M.HashMap String String
    , _labelIDs :: Stream.Stream Int
    , _functionNames :: Stream.Stream IR.FunctionID
    , _thunkNames :: Stream.Stream IR.FunctionID
    , _blockNames :: Stream.Stream IR.Label
    , _variableID :: Integer
    }

makeLenses ''CompileState

newtype CompilerInfo = CompilerInfo
    { _nameMap :: NameMap
    }

makeLenses ''CompilerInfo

newtype Compiler a = Compiler 
    { runCompiler :: ReaderT CompilerInfo (State CompileState) a
    }
    deriving (Functor, Applicative, Monad, MonadFix, MonadReader CompilerInfo, MonadState CompileState)

instance MonadIRBuilder Variable Compiler where
    addInstruction i = modify (blockStack . ix 0 . IR.iList %~ (:|> i))

data BindingAllocation
    = Thunk Value
    | TopLevelFunction Value NameMap

-- instance MonadTardis NameMap () Compiler where
--     getPast = Compiler getPast
--     getFuture = Compiler getFuture
--     sendPast = Compiler . sendPast
--     sendFuture = Compiler . sendFuture
--     tardis = Compiler . tardis

voidPtr :: IR.DataType
voidPtr = IR.Pointer (IR.FirstOrder IR.Void)

thunkFunc :: [IR.DataType] -> IR.DataType
thunkFunc args = IR.FunctionT (IR.FirstOrder IR.Void) (thunkArg : args)

thunkArg :: IR.DataType
thunkArg = IR.Pointer (IR.Structure [IR.NamedStruct B.thunkTagStruct [], voidPtr])

thunkStruct :: IR.Struct
thunkStruct = IR.Struct "thunk" ["T"] [IR.NamedStruct B.thunkTagStruct [], IR.TemplateArg "T"] False

wrapThunk :: IR.DataType -> IR.DataType
wrapThunk dt = IR.Pointer (IR.NamedStruct thunkStruct [dt])

isThunkType :: IR.DataType -> Bool
-- isThunkType (IR.Pointer (IR.Structure [IR.NamedStruct thunk _, _]))
--     | thunk == B.thunkTagStruct = True
isThunkType (IR.Pointer (IR.NamedStruct s _))
    | IR.structBaseName s == "thunk" = True
isThunkType (IR.Pointer dt) = isThunkType dt
isThunkType _ = False

returnType :: IR.DataType -> IR.DataType
returnType (IR.FunctionT ret _) = ret
returnType t = t

compile :: T.StaticContext -> T.MultiplicityPoset -> T.TypedExpr -> Program
compile staticContext poset expr =
    execState (runReaderT (runCompiler createProgram) startInfo) startState ^. compiledProgram
    where
        createProgram :: Compiler ()
        createProgram = do
            createDataTypes
            pushFunction (Just (AST.I "main")) (IR.FirstOrder IR.Void) []
            pushBlock
            programResult <- codegen (traceShowId (convertAST staticContext poset expr))
            printResult programResult
            ret Nothing
            popBlock
            void popFunction

        codegen :: CodegenExpr -> Compiler Value
        codegen (Let bindings body) = do
            -- First allocate objects where appropriate for each thunk. This includes creating "function
            -- headers" (i.e. pushing functions to the stack and using them as objects, but not "commiting" them)
            (allocVarMap, objects) <- unzip <$> mapM allocateThunk bindings
            -- Next, generate each complete binding in reverse order. This is necessary to ensure functions
            -- are built in the correct order - the top of the stack will be the last function.
            local (nameMap %~ M.union (M.fromList allocVarMap)) $ do
                zipWithM_ genBinding (reverse bindings) (reverse objects)
                codegen body
            where
                allocateThunk :: Binding -> Compiler ((Integer, Value), BindingAllocation)
                allocateThunk (LazyBinding name var (Lf captures [] body)) = do
                    captureTypes <- mapM lookupCaptureType captures
                    let thunkType = IR.Structure ( IR.NamedStruct B.thunkTagStruct []
                                                 : thunkFunc []
                                                 : captureTypes
                                                 )
                    forcedType <- ttypeToIRData M.empty (varType var)

                    thunkVar <- malloc (mkVar Strict) thunkType
                    thunkObject <- bitcast (mkVar Lazy) thunkVar forcedType
                    pure ((varID (baseVar var), thunkObject), Thunk thunkVar)

                allocateThunk (LazyBinding name var (Lf [] args body)) = do
                    (argRegs, argVarMap) <- mapAndUnzipM makeArgument args
                    let varMap = M.fromList argVarMap
                    varDataType <- ttypeToIRData M.empty (varType var)
                    funcVal <- pushFunction name (returnType varDataType) argRegs
                    pure ((varID (baseVar var), funcVal), TopLevelFunction funcVal (M.fromList argVarMap))

                allocateThunk (LazyBinding name var (Lf captures args body)) = do
                    functionType <- ttypeToIRData M.empty (varType var)
                    let IR.FunctionT retType argTypes = functionType
                        funcType = IR.FunctionT retType (voidPtr : argTypes)
                    captureTypes <- mapM lookupCaptureType captures
                    let closureType = IR.Structure
                                          ( funcType
                                          : captureTypes
                                          )

                    clVar <- malloc (mkVar Strict) closureType
                    pure ((varID (baseVar var), clVar), Thunk clVar)

                genBinding :: Binding -> BindingAllocation -> Compiler ()
                genBinding (LazyBinding name var (Lf captures [] body)) (Thunk thunkVar) = do
                    forcedType <- ttypeToIRData M.empty (varType var)

                    -- Create the new thunk function - note that this doesn't affect
                    -- the block we are creating at this point, so instructions will
                    -- still be added to the entry block!
                    -- We do this to get the name of thunk.
                    thunkArgReg <- mkArg Lazy
                    let thunkArg = IR.ValVariable forcedType thunkArgReg
                    thunkFuncVal <- createFreshThunk name (IR.FirstOrder IR.Void) [(thunkArgReg, forcedType)]

                    -- Write a tag to indicate that the thunk has not
                    -- been evaluated
                    -- Write the function address
                    -- Write the captured variables into the closure
                    tagPtr <- getElementPtr (mkVar Strict) thunkVar [0, 0]
                    write (mkInt1 False) tagPtr
                    thunkFuncPtr <- getElementPtr (mkVar Strict) thunkVar [1]
                    write thunkFuncVal thunkFuncPtr
                    zipWithM_ (writeCapture thunkVar) captures [2..]

                    ----- THUNK -----

                    -- Now we start to generate the thunk code itself
                    pushBlock

                    -- Unpack the captured variabes from the closure
                    thunkArgCast <- bitcast (mkVar Strict) thunkArg (IR.datatype thunkVar)
                    closureVars <- M.fromList <$> zipWithM (readCapture thunkArgCast) captures [2..]

                    -- Now, we run the regular, strict code generator for the body.
                    thunkResult <- local ( (nameMap %~ M.union closureVars)
                                         . (nameMap %~ M.insert (varID (baseVar var)) thunkArg)
                                         ) $ codegen body

                    -- Overwrite the thunk
                    tagPtr <- getElementPtr (mkVar Strict) thunkArg [0, 0]
                    write (mkInt1 True) tagPtr

                    writebackAddr <- getElementPtr (mkVar Strict) thunkArg [1]
                    write thunkResult writebackAddr

                    ret Nothing
                    popBlock
                    -- Now, we pop the top function on the stack. This function is the thunk
                    -- generator.
                    void popFunction

                genBinding (LazyBinding name var (Lf [] args body)) (TopLevelFunction funcVal varMap) = do
                    pushBlock
                    result <- local ( (nameMap %~ M.union varMap)
                                    . (nameMap %~ M.insert (varID (baseVar var)) funcVal)
                                    ) $ codegen body
                    ret (Just result)
                    popBlock
                    void popFunction

                genBinding (LazyBinding name var (Lf captures args body)) (Thunk clVar) = do
                    functionType <- ttypeToIRData M.empty (varType var)
                    let IR.FunctionT retType argTypes = functionType
                        funcType = IR.FunctionT retType (voidPtr : argTypes)
                    captureTypes <- mapM lookupCaptureType captures
                    let closureType = IR.Structure
                                          ( funcType
                                          : captureTypes
                                          )

                    clArgReg <- mkArg Strict
                    let clArgVar = IR.ValVariable (IR.Pointer closureType) clArgReg

                    (argRegs, argVarMap) <- mapAndUnzipM makeArgument args

                    funcVal <- pushFunction name retType ((clArgReg, IR.Pointer closureType):argRegs)

                    funcPtr <- getElementPtr (mkVar Strict) clVar [0]
                    write funcVal funcPtr
                    zipWithM_ (writeCapture clVar) captures [1..]
                    
                    -- Now we start to generate the function
                    pushBlock

                    -- Unpack the captured variabes from the closure
                    closureVars <- M.fromList <$> zipWithM (readCapture clArgVar) captures [1..]

                    -- Now, we run the regular, strict code generator for the body.
                    result <- local ( (nameMap %~ M.union closureVars . M.union (M.fromList argVarMap))
                                    . (nameMap %~ M.insert (varID (baseVar var)) clArgVar)
                                    ) $ codegen body

                    ret (Just result)

                    popBlock
                    void popFunction

                -- genBinding (EagerBinding _ var body) = do
                --     res <- local (recursiveStrict %~ S.insert (baseVar var)) $ codegen body
                --     pure (varID (baseVar var), res)
                --     -- fst <$> unpackPattern (throw 1) pat res

                writeCapture :: Value -> Var -> Int -> Compiler ()
                writeCapture base v offset = do
                    capVal <- lookupVar v
                    capPtr <- getElementPtr (mkVar Strict) base [offset]
                    write capVal capPtr

                readCapture :: Value -> Var -> Int -> Compiler (Integer, Value)
                readCapture base v offset = do
                    addr <- getElementPtr (mkVar Strict) base [offset]
                    evalType <- evaluation <$> lookupVar v
                    val <- read (mkVar evalType) addr
                    pure (varID v, val)

                makeArgument :: TypedVar -> Compiler ((Variable, IR.DataType), (Integer, Value))
                makeArgument v = do
                    let eval = if isBoxed (varType v)
                                  then Lazy
                                  else Strict
                    arg <- mkArg eval
                    varDataType <- ttypeToIRData M.empty (varType v)
                    pure ((arg, varDataType), (varID (baseVar v), IR.ValVariable varDataType arg))

                lookupCaptureType :: Var -> Compiler IR.DataType
                lookupCaptureType v = do
                    fwdVal <- asks (M.lookup (varID v) . (^. nameMap))
                    pure (maybe (wrapThunk voidPtr) IR.datatype fwdVal)

                addMutualValue :: Integer -> Value -> Rev.StateT NameMap Compiler ()
                addMutualValue name val = do
                    Rev.modify (M.insert name val)
    
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
                genBranches :: IR.Label -> Value -> [Alternative] -> Compiler [PhiNode]
                genBranches _ _ [] = do
                    throw 123
                    pure []
                genBranches successLabel var (Alt pattern expr:rest) = do
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
                    names <- unpackPattern failLabel pattern var
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

        codegen (Application fun []) = do
            funVal <- lookupVar fun
            forceCompute funVal

        codegen (Application fun args) = do
            funVal <- lookupVar fun
            forcedFunVal <- forceCompute funVal
            argVals <- forM args $ \case
                Var v -> lookupVar v
                Lit l -> genLiteral l
            if IR.isFunctionType (IR.datatype forcedFunVal)
               then call (mkVar Strict) forcedFunVal argVals
               else do
                   funcPtr <- getElementPtr (mkVar Strict) forcedFunVal [0]
                   func <- read (mkVar Strict) funcPtr
                   call (mkVar Strict) func (forcedFunVal : argVals)
                
        codegen (PrimApp fun args) = do
            argVals <- forM args $ \case
                Var v -> lookupVar v >>= forceCompute
                Lit l -> genLiteral l
            forced <- mapM forceCompute argVals
            B.generatePrimitive (mkVar Strict) fun forced

        codegen (ConsApp consId@(AST.I cons) args) = do
            consFunc <- gets ((^. consFunction) . (M.! consId) . (^. dataConsInfo))
            argVals <- forM args $ \case
                Var v -> lookupVar v
                Lit l -> genLiteral l
            call (mkVar Strict) consFunc argVals
            -- resultDataType <- ttypeToIRData retTy
            -- bitcast (mkVar Strict) funcRes resultDataType

        -- codegen (Literal lit) = genLiteral lit
        --     where

        codegen (PackedTuple vs) = do
            elemTypes <- mapM argType vs
            tuplePtr <- malloc (mkVar Strict) (IR.Structure elemTypes)
            zipWithM_ (writeVal tuplePtr) vs [0..]
            pure tuplePtr
            where
                argType :: Atom -> Compiler IR.DataType
                argType (Var v) = IR.datatype <$> lookupVar v
                argType (Lit (IntLiteral _)) = pure (IR.FirstOrder IR.Int64T)
                argType (Lit (RealLiteral _)) = pure (IR.FirstOrder IR.Real64T)

                getValue :: Atom -> Compiler Value
                getValue (Var v) = lookupVar v
                getValue (Lit l) = genLiteral l

                writeVal :: Value -> Atom -> Int -> Compiler ()
                writeVal base atom offset = do
                    elemPtr <- getElementPtr (mkVar Strict) base [offset]
                    val <- getValue atom
                    write val elemPtr

        codegen (Projector offset v) = do
            base <- lookupVar v
            forced <- forceCompute base
            addr <- getElementPtr (mkVar Strict) forced [offset]
            value <- read (mkVar Lazy) addr
            forceCompute value

        codegen (Free var expr) = do
            freeVar <- lookupVar var
            addInstruction $ IR.Free freeVar
            codegen expr

        codegen Error = do
            throw 321
            pure (IR.ValImmediate IR.Undef)

        lookupVar :: Var -> Compiler Value
        lookupVar v = asks ((M.! varID v) . (^. nameMap))

        genLiteral :: PrimitiveLiteral -> Compiler Value
        genLiteral (IntLiteral i) = pure (mkInt i)
        genLiteral (RealLiteral r) = pure (IR.ValImmediate (IR.Real64 r))

        forceCompute :: Value -> Compiler Value
        forceCompute addr@(IR.ValVariable dt (Variable Lazy _)) = force addr dt
        forceCompute addr@(IR.ValVariable dt (Argument Lazy _)) = force addr dt
        forceCompute v = pure v

        force :: Value -> IR.DataType -> Compiler Value
        force baseAddr dt = do
            -- We start with the entry block stack like:
            --  ... | entry
            -- We add instructions to start the test to see if the value
            -- has been evaluated
            evalTagPtr <- getElementPtr (mkVar Strict) baseAddr [0, 0]
            evalTag <- read (mkVar Strict) evalTagPtr
            evaluated <- binop IR.Equal (mkVar Strict) evalTag (mkInt1 True)

            -- Get the payload pointer
            payloadPtr <- getElementPtr (mkVar Strict) baseAddr [1]

            -- Next, we push the "force" block:
            --  ... | entry | force
            pushBlock

            -- Read the call address out of the closure. This is in the payload location
            callTargetPtr <- bitcast (mkVar Strict) payloadPtr (IR.Pointer (thunkFunc []))
            callTarget <- read (mkVar Strict) callTargetPtr
            -- Call the thunk
            voidCall callTarget [baseAddr]

            -- Now, we swap the blocks. This is to avoid the entry block being buried
            -- later on. Then, we push the "rest" block.
            --  ... | force | entry | rest
            swapBlocks
            pushBlock
            
            restLabel <- blockLabel

            -- We now read out the result variable from the payload
            payload <- read (mkVar Strict) payloadPtr

            -- Now we swap the top two blocks. This is because we wish to pop the entry
            -- then force blocks.
            --  ... | force | rest | entry
            swapBlocks

            -- Add the branch instruction to skip over the force block in the case that
            -- the thunk has already been forced
            branch evaluated restLabel

            -- Pop, then swap, then pop again to apply the entry then force blocks
            popBlock
            swapBlocks
            popBlock

            pure payload

        unpackPattern :: IR.Label -> Pattern -> Value -> Compiler NameMap
        unpackPattern failLabel pattern v = do
            unpack pattern v

            -- if patternCanFail
            --    then do
            --        pushBlock
            --        failResult <- onFail
            --        popBlock
            --        pure (nameMap, Just failResult)
            --    else pure (nameMap, Nothing)
            where
                unpack :: Pattern -> Value -> Compiler NameMap
                unpack (VarPattern name) var =
                    pure (M.singleton (varID (baseVar name)) var)
                unpack (ConsPattern cons args) var = do
                    forced <- forceCompute var
                    consInfo <- gets ((M.! cons) . (^. dataConsInfo))
                    case consInfo ^. altTag of
                      Nothing -> do
                          nameMaps <- zipWithM (unpackElem forced) args [[i] | i <- [0..]]
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
                          tagPtr <- bitcast (mkVar Strict) forced (IR.Pointer IR.i64)
                          tagVal <- read (mkVar Strict) tagPtr
                          cmp <- binop IR.NotEqual (mkVar Strict) tagVal (mkInt index)
                          branch cmp failLabel
                          -- Pop the entry block
                          --    ... | rest

                          -- let branchType = IR.Pointer (IR.Structure [IR.i64, IR.specialise (zip argNames argTypes) (consInfo ^. consDataType)])
                          popBlock
                          let branchType = IR.Pointer (IR.Structure [IR.i64, consInfo ^. consDataType])
                          branchPtr <- bitcast (mkVar Strict) forced branchType
                          nameMaps <- zipWithM (unpackElem branchPtr) args [[1, i] | i <- [0..]]
                          pure (M.unions nameMaps)
                unpack (TuplePattern ts) var = do
                    forced <- forceCompute var
                    nameMaps <- zipWithM (unpackElem forced) ts [[i] | i <- [0..]]
                    pure (M.unions nameMaps)
                unpack (LitPattern lit) var = do
                    forced <- forceCompute var
                    unpackLit forced lit
                    where
                        unpackLit :: Value -> PrimitiveLiteral -> Compiler NameMap
                        unpackLit forced (IntLiteral i) = literalMatcher forced (mkInt i)
                        unpackLit forced (RealLiteral r) = literalMatcher forced (IR.ValImmediate (IR.Real64 r))

                        literalMatcher :: Value -> Value -> Compiler NameMap
                        literalMatcher forced checkValue = do
                            cmp <- binop IR.NotEqual (mkVar Strict) forced checkValue
                            branch cmp failLabel
                            popBlock
                            pushBlock
                            pure M.empty
                            -- -- Entry:
                            -- --  ... | entry
                            -- -- First, push the "rest" block:
                            -- --  ... | entry | rest
                            -- pushBlock
                            -- restLabel <- blockLabel

                            -- -- Now, swap so entry is on top:
                            -- --  ... | rest | entry
                            -- swapBlocks
                            -- cmp <- binop IR.Equal (mkVar Strict) forced checkValue
                            -- branch cmp restLabel

                            -- -- Then, pop the entry block:
                            -- --  ... | rest
                            -- popBlock

                            -- -- We don't bind any vars in a literal pattern
                            -- pure M.empty
                
                unpackElem :: Value -> Pattern -> [Int] -> Compiler NameMap
                unpackElem forced pat index = do
                    elemPtr <- getElementPtr (mkVar Strict) forced index
                    let elemEval
                            | isThunkType (IR.datatype elemPtr) = Lazy
                            | otherwise = Strict
                    elem <- read (mkVar elemEval) elemPtr
                    unpack pat elem

        createFreshThunk :: Maybe AST.Identifier -> IR.DataType -> [(Variable, IR.DataType)]
                         -> Compiler Value
        createFreshThunk = addFunctionToStack thunkNames

        pushFunction :: Maybe AST.Identifier -> IR.DataType -> [(Variable, IR.DataType)]
                     -> Compiler Value
        pushFunction = addFunctionToStack functionNames

        addFunctionToStack :: Lens' CompileState (Stream.Stream IR.FunctionID) -> Maybe AST.Identifier
                           -> IR.DataType
                           -> [(Variable, IR.DataType)]
                           -> Compiler Value
        addFunctionToStack nameSource name retType args = do
            funcName <- maybe (popName nameSource) extractName name
            let func = IR.makeFunc funcName retType args
            modify (funcStack %~ (func:))
            pure (IR.functionValue func)
            where
                extractName :: AST.Identifier -> Compiler IR.FunctionID
                extractName (AST.I n) = pure (IR.FID n)

        popFunction :: Compiler Function
        popFunction = do
            (fn, rest) <- gets (uncons . (^. funcStack))
            modify (funcStack .~ rest)
            modify (compiledProgram %~ IR.addFunction fn)
            pure fn
            where
                uncons :: [a] -> (a, [a])
                uncons (x:xs) = (x, xs)

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

        ttypeToIRData :: M.HashMap T.TypeVar IR.DataType -> TranslateType -> Compiler IR.DataType
        ttypeToIRData _ IntT = pure IR.i64
        ttypeToIRData _ RealT = pure IR.r64
        ttypeToIRData pmap (Poly p) =
            case M.lookup p pmap of
              Just t -> pure t
              Nothing -> pure voidPtr
        ttypeToIRData pmap (Tuple ts) = IR.Pointer . IR.Structure <$> mapM (ttypeToIRData pmap) ts
        ttypeToIRData _ (Named (AST.I name)) = do
            val <- gets  (M.lookup name . (^. dataTypeInfo))
            case val of
              Just v -> pure (IR.Pointer (IR.NamedStruct (v ^. baseType) []))
              Nothing -> pure voidPtr -- error (show name) TODO: Think about this
        ttypeToIRData pmap (Function ret args) = IR.FunctionT <$> ttypeToIRData pmap ret <*> mapM (ttypeToIRData pmap) args
        ttypeToIRData pmap (TypeApp (AST.I name) args) = do
            val <- gets (M.lookup name . (^. dataTypeInfo))
            argDataTypes <- mapM (ttypeToIRData pmap) args
            case val of
              Just v -> pure (IR.Pointer (IR.NamedStruct (v ^. baseType) argDataTypes))
              Nothing -> error (show name)
        ttypeToIRData pmap (Boxed t) = wrapThunk <$> ttypeToIRData pmap t
        
        -- convertStrictData :: TranslateType -> Compiler IR.DataType
        -- convertStrictData IntT = pure IR.i64
        -- convertStrictData RealT = pure IR.r64
        -- convertStrictData Poly = pure voidPtr
        -- convertStrictData (Tuple ts) = IR.Pointer . IR.Structure <$> mapM ttypeToIRData ts
        -- convertStrictData (Named name) = do
        --     val <- gets (M.lookup name . (^. dataConsTypes))
        --     case val of
        --       Just v -> pure (IR.Pointer v)
        --       Nothing -> error (show name)
        --         -- gets (IR.Pointer . (M.! name) . (^. dataConsTypes))
        -- convertStrictData (Function ret args) = IR.FunctionT <$> convertStrictData ret <*> mapM ttypeToIRData args
        -- convertStrictData (MkStrict t) = convertStrictData t
        
        createDataTypes :: Compiler ()
        createDataTypes = do
            modify (compiledProgram %~ IR.addStruct B.thunkTagStruct)
            modify (compiledProgram %~ IR.addStruct thunkStruct)
            let programDataTypes = M.toList (staticContext ^. T.dataTypes)
            mapM_ (\(tn, (tvs, _)) -> forwardDeclType tn tvs) programDataTypes
            mapM_ (uncurry createDataType) programDataTypes
            -- forM_ (M.toList (staticContext ^. T.dataTypes)) $ \(typeId@(AST.I typeName), constructors) ->
            --     case constructors of
            --       [cons] -> do
            --           undefined
            --       _ -> do
            --           consTypes <- mapM (createDataConstructor typeName) constructors
            --           let union = IR.Union ("_type_" ++ typeName) (map fst consTypes)
            --               unionDataType = IR.NamedStruct union
            --           modify (compiledProgram %~ IR.addStruct union)
            --           modify (dataConsTypes %~ M.insert typeId unionDataType)
            --           zipWithM_ (createConsFunction unionDataType) (zip constructors [0..]) consTypes
        
        forwardDeclType :: AST.Identifier -> S.HashSet T.TypeVar -> Compiler ()
        forwardDeclType (AST.I typeName) tvs = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])
                fdecl = IR.ForwardDecl ("_type_" ++ typeName) typeVars
                info = DataTypeInfo fdecl (listArray (0, -1) []) True
            modify (compiledProgram %~ IR.addStruct fdecl)
            modify (dataTypeInfo %~ M.insert typeName info)

        createDataType :: AST.Identifier
                       -> (S.HashSet T.TypeVar, [(AST.Identifier, (T.TypeScheme, [T.Type]))])
                       -> Compiler ()
        createDataType (AST.I typeName) (tvs, []) = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])

            let union = IR.Union ("_type_" ++ typeName) typeVars Nothing []
            modify (compiledProgram %~ IR.addStruct union)
            let info = DataTypeInfo union (listArray (0, -1) []) True
            modify (dataTypeInfo %~ M.insert typeName info)

        createDataType (AST.I typeName) (tvs, [(cons, (_, argTypes))]) = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])
                typeVArgs = map IR.TemplateArg typeVars
                typeVarMap = M.fromList (zip (S.toList tvs) typeVars)

            (consStruct, components) <- createDataConstructor typeName typeVars typeVarMap argTypes cons
            let alias = IR.Alias ("_type_" ++ typeName) typeVars consStruct
                aliasDataType = IR.NamedStruct alias typeVArgs

            consInfo <- createConsFunction aliasDataType (cons, Nothing) (consStruct, components)
            let info = DataTypeInfo alias (listArray (0, 0) [consInfo]) False

            modify (dataTypeInfo %~ M.insert typeName info)
            modify (compiledProgram %~ IR.addStruct alias)
            modify (symbolRefs %~ M.insert (IR.structBaseName alias) typeName)

        createDataType (AST.I typeName) (tvs, conss) = do
            let typeVars = take (S.size tvs) (map (\i -> "T" ++ show i) [0..])
                typeVArgs = map IR.TemplateArg typeVars
                typeVarMap = M.fromList (zip (S.toList tvs) typeVars)

            consTypes <- mapM (\(cons, (_, args)) -> createDataConstructor typeName typeVars typeVarMap args cons) conss
            let union = IR.Union ("_type_" ++ typeName) typeVars (Just IR.i64) (map fst consTypes)
                unionDataType = IR.NamedStruct union typeVArgs

            consInfos <- zipWithM (createConsFunction unionDataType) (zip (map fst conss) (map Just [0..])) consTypes
            let info = DataTypeInfo union (listArray (0, length conss - 1) consInfos) True

            modify (dataTypeInfo %~ M.insert typeName info)
            modify (compiledProgram %~ IR.addStruct union)
            modify (symbolRefs %~ M.insert (IR.structBaseName union) typeName)

        createDataConstructor :: String -> [IR.TemplateArgName] -> M.HashMap T.TypeVar IR.TemplateArgName
                              -> [T.Type] -> AST.Identifier
                              -> Compiler (IR.DataType, [IR.DataType])
        createDataConstructor typeName tArgs subMap argTypes consId@(AST.I consName) = do
            componentDataTypes <- mapM (ttypeToIRData (M.map IR.TemplateArg subMap) . ttype) argTypes
            let consSymbol = "_cons_" ++ typeName ++ "__" ++ consName
                consDataStruct = IR.Struct consSymbol tArgs componentDataTypes False

            modify (compiledProgram %~ IR.addStruct consDataStruct)
            modify (symbolRefs %~ M.insert consSymbol consName)
            pure (IR.NamedStruct consDataStruct (map IR.TemplateArg tArgs), componentDataTypes)
            -- where
            --     findType :: T.Type -> Compiler IR.DataType
            --     findType (T.Poly a) =
            --         pure (IR.Pointer (IR.NamedStruct thunkStruct [IR.TemplateArg (subMap M.! a)]))
            --     findType t = ttypeToIRData (ttype t)

        createConsFunction :: IR.DataType -> (AST.Identifier, Maybe Int) -> (IR.DataType, [IR.DataType])
                           -> Compiler ConsInfo
        createConsFunction baseDataType (consId@(AST.I consName), altIndex) (consDataType, argTypes) = do
            funcArgs <- mapM (\dt -> (,dt) <$> mkArg Strict) argTypes
            funcVal <- pushFunction (Just (AST.I "_cons_" <> consId)) (IR.Pointer baseDataType) funcArgs
            pushBlock

            dataPtr <- malloc (mkVar Strict) baseDataType
            case altIndex of
              Nothing -> zipWithM_ (writeArgElement dataPtr) funcArgs [0..]
              Just index -> do
                  castPtr <- bitcast (mkVar Strict) dataPtr (IR.Pointer (IR.Structure (IR.i64 : argTypes)))
                  altTagPtr <- getElementPtr (mkVar Strict) castPtr [0]
                  write (mkInt index) altTagPtr
                  zipWithM_ (writeArgElement castPtr) funcArgs [1..]

            ret (Just dataPtr)

            popBlock
            popFunction

            let info = ConsInfo consDataType funcVal altIndex

            modify (dataConsInfo %~ M.insert consId info)
            pure info
            where
                writeArgElement :: Value -> (Variable, IR.DataType) -> Int -> Compiler ()
                writeArgElement basePtr (var, varType) index = do
                    elemPtr <- getElementPtr (mkVar Strict) basePtr [index]
                    write (IR.ValVariable varType var) elemPtr

        printResult :: Value -> Compiler ()
        printResult result = do
            forced <- forceCompute result
            printVal (IR.datatype forced) forced
            printf "\n" []
            where
                printVal :: IR.DataType -> Value -> Compiler ()
                printVal (IR.FirstOrder fo) val = printFirstOrder fo val
                printVal (IR.Pointer (IR.NamedStruct named args)) val = printNamed named args val
                printVal (IR.Pointer (IR.Structure ts)) val = do
                    printf "(" []
                    intercalatePrintM ", " (zipWith (printSubValue val) ts [0..])
                    printf ")" []
                printVal (IR.FunctionT ret args) val = do
                    printf "fun" []
                printVal (IR.Pointer t) val = do
                    printf "ptr" []
                printVal t _ = pure () -- error (show t)

                printFirstOrder :: IR.FirstOrder -> Value -> Compiler ()
                printFirstOrder IR.Int1T val = pure ()
                printFirstOrder IR.Int64T val = do
                    printf "%d" [val]
                printFirstOrder IR.Real64T val = do
                    printf "%f" [val]
                printFirstOrder IR.UnitT val = do
                    printf "()" []
                printFirstOrder IR.Void val = do
                    printf "error" []

                printNamed :: IR.Struct -> [IR.DataType] -> Value -> Compiler ()
                printNamed (IR.Struct symbol argNames [] _) argTypes val = do
                    name <- gets ((M.! symbol) . (^. symbolRefs))
                    printf name []
                printNamed (IR.Struct symbol argNames ts _) argTypes val = do
                    name <- gets ((M.! symbol) . (^. symbolRefs))
                    printf ("(" ++ name ++ " ") []
                    intercalatePrintM " " (zipWith (printSubValue val) (map (IR.specialise (zip argNames argTypes)) ts) [0..])
                    printf ")" []
                printNamed (IR.Union _ argNames Nothing ts) argTypes val = do
                    printf "untagged-union" []
                printNamed (IR.Union symbol argNames (Just tag) ts) argTypes val = do
                    tagPtr <- bitcast (mkVar Strict) val (IR.Pointer IR.i64)
                    tag <- read (mkVar Strict) tagPtr
                    pushBlock
                    restLabel <- blockLabel
                    swapBlocks
                    name <- gets ((M.! symbol) . (^. symbolRefs))
                    typeInfo <- gets ((M.! name) . (^. dataTypeInfo))
                    matchTag restLabel tag val (assocs (typeInfo ^. alternatives))
                    popBlock
                    where
                        matchTag :: IR.Label -> Value -> Value -> [(Int, ConsInfo)] -> Compiler ()
                        matchTag successLabel _ _ [] = jump successLabel
                        matchTag successLabel tagVal dataPtr ((tag, consInfo):ts) = do
                            -- Entry:
                            --  ... | entry
                            -- Push match block:
                            --  ... | entry | match
                            pushBlock
                            matchLabel <- blockLabel
                            -- Swap blocks:
                            --  ... | match | entry
                            swapBlocks
                            cmp <- binop IR.Equal (mkVar Strict) tagVal (mkInt tag)
                            branch cmp matchLabel
                            -- Pop entry:
                            --  ... | match
                            popBlock
                            -- Push other branches:
                            --  ... | match | entry'
                            pushBlock
                            matchTag successLabel tagVal dataPtr ts
                            -- Pop branch return:
                            --  ... | match
                            popBlock
                            -- Display this branch
                            let branchType = IR.Pointer (IR.Structure [IR.i64, IR.specialise (zip argNames argTypes) (consInfo ^. consDataType)])
                            branchPtr <- bitcast (mkVar Strict) dataPtr branchType
                            altPtr <- getElementPtr (mkVar Strict) branchPtr [1]
                            printVal (IR.datatype altPtr) altPtr
                            jump successLabel
                printNamed (IR.Alias _ argNames t) argTypes val = printVal (IR.Pointer (IR.specialise (zip argNames argTypes) t)) val
                printNamed s@(IR.ForwardDecl symbol _) argTypes val = do
                    name <- gets ((M.! symbol) . (^. symbolRefs))
                    typeInfo <- gets ((M.! name) . (^. dataTypeInfo))
                    printNamed (typeInfo ^. baseType) argTypes val

                intercalatePrintM :: String -> [Compiler ()] -> Compiler ()
                intercalatePrintM _ [] = pure ()
                intercalatePrintM _ [printer] = printer
                intercalatePrintM sep (printer:printers) = do
                    printer
                    printf sep []
                    intercalatePrintM sep printers

                printSubValue :: Value -> IR.DataType -> Int -> Compiler ()
                printSubValue base dt index = do
                    elemPtr <- getElementPtr (mkVar Strict) base [index]
                    let elemEval
                            | isThunkType (IR.datatype elemPtr) = Lazy
                            | otherwise = Strict
                    elem <- read (mkVar elemEval) elemPtr
                    forcedElem <- forceCompute elem
                    printVal (IR.datatype forcedElem) forcedElem

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
            , _symbolRefs = M.empty
            , _labelIDs = Stream.iterate (+1) 0
            , _functionNames = fmap (\f -> IR.FID ("__anonymous_" ++ show f)) (Stream.iterate (+1) 0)
            , _thunkNames = fmap (\f -> IR.FID ("__thunk_" ++ show f)) (Stream.iterate (+1) 0)
            , _blockNames = fmap (\b -> IR.Label ("block_" ++ show b)) (Stream.iterate (+1) 0)
            , _variableID = 0
            }
        
        startInfo :: CompilerInfo
        startInfo = CompilerInfo
            { _nameMap = M.empty
            }

testEverything2 :: String -> IO ()
testEverything2 s = case typecheck Builtin.Builtin.defaultBuiltins (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (T.showError s tvm e)
                     Right (t, p) -> print (compile Builtin.Builtin.defaultBuiltins p t) 
    where
        fromRight (Right x) = x

testCompile :: String -> Program
testCompile s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck Builtin.Builtin.defaultBuiltins parsed
     in compile Builtin.Builtin.defaultBuiltins poset typed
