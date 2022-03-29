{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.Sequence as Seq hiding (zip, zipWith, unzip)
import Data.Bifunctor (bimap)
import Data.Maybe (catMaybes, fromMaybe, fromJust)
import Data.Word
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
import Control.Monad.State
import Control.Monad.Reader
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

data Evaluation
    = Strict
    | Lazy
    deriving (Eq, Generic)

instance Hashable Evaluation

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

data CompileState = CompileState
    { _blockStack :: [BasicBlock]
    , _funcStack :: [Function]
    , _compiledProgram :: Program
    , _labelIDs :: Stream.Stream Int
    , _functionNames :: Stream.Stream IR.FunctionID
    , _thunkNames :: Stream.Stream IR.FunctionID
    , _blockNames :: Stream.Stream IR.Label
    , _variableID :: Integer
    }

makeLenses ''CompileState

data CompilerInfo = CompilerInfo
    { _nameMap :: NameMap
    , _recursiveStrict :: S.HashSet Var
    }

makeLenses ''CompilerInfo

newtype Compiler a = Compiler { runCompiler :: ReaderT CompilerInfo (State CompileState) a }
    deriving (Functor, Applicative, Monad, MonadState CompileState, MonadReader CompilerInfo)

instance MonadIRBuilder Variable Compiler where
    addInstruction i = modify (blockStack . ix 0 . IR.iList %~ (:|> i))

compile :: T.TypedExpr -> T.MultiplicityPoset -> Program
compile expr poset = execState (runReaderT (runCompiler finalise) startInfo) startState ^. compiledProgram
    where
        finalise :: Compiler ()
        finalise = do
            pushFunction (Just (AST.I "main")) []
            pushBlock
            programResult <- codegen (convertAST expr poset)
            forced <- forceCompute programResult
            ret (Just forced)
            popBlock
            void popFunction

        codegen :: CodegenExpr -> Compiler Value
        codegen (Let bindings body) = do
            boundVars <- M.fromList <$> mapM genBinding bindings
            local (nameMap %~ M.union boundVars) $ codegen body
            where
                genBinding :: Binding -> Compiler (Integer, Value)
                genBinding (LazyBinding name var (Lf captures [] body)) = do
                    let thunkType = IR.Structure 
                                        ( IR.NamedStruct B.thunkTagStruct
                                        : thunkFunc []
                                        : map varType captures
                                        )

                    thunkReg <- mkVar Strict

                    -- Create the new thunk function - note that this doesn't affect
                    -- the block we are creating at this point, so instructions will
                    -- still be added to the entry block!
                    -- We do this to get the name of thunk.
                    thunkArgReg <- mkArg Lazy
                    let thunkArg = IR.ValVariable (varType var) thunkArgReg
                    thunkName <- createFreshThunk name [thunkArgReg]

                    -- Add an instruction to allocate the memory
                    -- Write a tag to indicate that the thunk has not
                    -- been evaluated
                    -- Write the function address
                    -- Write the captured variables into the closure
                    thunkVar <- malloc (pure thunkReg) thunkType
                    tagPtr <- getElementPtr (mkVar Strict) thunkVar [0, 0]
                    write (mkInt1 False) tagPtr
                    thunkPtr <- getElementPtr (mkVar Strict) thunkVar [1]
                    write (IR.ValFunction (thunkFunc []) thunkName) thunkPtr
                    zipWithM_ (writeCapture thunkVar) captures [2..]

                    thunkObject <- bitcast (mkVar Lazy) thunkVar (varType var)

                    ----- THUNK -----

                    -- Now we start to generate the thunk code itself
                    pushBlock

                    -- Unpack the captured variabes from the closure
                    thunkArgCast <- bitcast (mkVar Strict) thunkArg (IR.Pointer thunkType)
                    closureVars <- M.fromList <$> zipWithM (readCapture thunkArgCast) captures [2..]

                    -- Now, we run the regular, strict code generator for the body.
                    thunkResult <- local ( (nameMap %~ M.union closureVars)
                                         . (nameMap %~ M.insert (varID var) thunkArg)
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
                    popFunction

                    pure (varID var, thunkObject)

                genBinding (LazyBinding name var (Lf [] args body)) = do
                    (argRegs, argVarMap) <- mapAndUnzipM makeArgument args
                    let varMap = M.fromList argVarMap
                    func <- pushFunction name argRegs
                    let funcVal = IR.ValFunction (varType var) func
                    pushBlock
                    result <- local ( (nameMap %~ M.union varMap)
                                    . (nameMap %~ M.insert (varID var) funcVal)
                                    ) $ codegen body
                    ret (Just result)
                    popBlock
                    popFunction
                    pure (varID var, funcVal)

                genBinding (LazyBinding name var (Lf captures args body)) = do
                    let funcType = thunkFunc (map (varType . snd) args)
                    let closureType = IR.Structure
                                          ( funcType
                                          : map varType captures
                                          )
                    clReg <- mkVar Strict

                    clArgReg <- mkArg Strict
                    let clArgVar = IR.ValVariable (IR.Pointer closureType) clArgReg

                    (argRegs, argVarMap) <- mapAndUnzipM makeArgument args
                    let varMap = M.fromList argVarMap

                    funcName <- pushFunction name (clArgReg:argRegs)

                    capVals <- mapM (\v -> asks ((M.! varID v) . (^. nameMap))) captures
                    -- let clVal = IR.ValStruct 
                    --                 ( IR.Value (IR.ValFunction funcType funcName)
                    --                 : map IR.Value capVals
                    --                 )
                    let clVal = IR.ValImmediate (IR.Int1 False)

                    clVar <- malloc (pure clReg) closureType
                    funcPtr <- getElementPtr (mkVar Strict) clVar [0]
                    write (IR.ValFunction funcType funcName) funcPtr
                    zipWithM_ (writeCapture clVar) captures [1..]
                    
                    -- Now we start to generate the function
                    pushBlock

                    -- Unpack the captured variabes from the closure
                    closureVars <- M.fromList <$> zipWithM (readCapture clArgVar) captures [1..]

                    -- Now, we run the regular, strict code generator for the body.
                    result <- local ( (nameMap %~ M.union closureVars . M.union varMap)
                                    . (nameMap %~ M.insert (varID var) clArgVar)
                                    ) $ codegen body

                    ret (Just result)

                    popBlock
                    popFunction
                    pure (varID var, clVar)

                genBinding (EagerBinding _ var body) = do
                    res <- local (recursiveStrict %~ S.insert var) $ codegen body
                    pure (varID var, res)
                    -- fst <$> unpackPattern (throw 1) pat res

                writeCapture :: Value -> Var -> Int -> Compiler ()
                writeCapture base v offset = do
                    capVal <- asks ((M.! varID v) . (^. nameMap))
                    capPtr <- getElementPtr (mkArg Strict) base [offset]
                    write capVal capPtr

                readCapture :: Value -> Var -> Int -> Compiler (Integer, Value)
                readCapture base v offset = do
                    addr <- getElementPtr (mkVar Strict) base [offset]
                    evalType <- asks (evaluation . (M.! varID v) . (^. nameMap))
                    val <- read (mkVar evalType) addr
                    pure (varID v, val)

                makeArgument :: (Bool, Var) -> Compiler (Variable, (Integer, Value))
                makeArgument (eager, v) = do
                    arg <- if eager
                              then mkArg Strict
                              else mkArg Lazy
                    pure (arg, (varID v, IR.ValVariable (varType v) arg))

        codegen (Case disc branches) = do
            discVal <- codegen disc
            pushBlock
            restLabel <- blockLabel
            swapBlocks
            phiNodes <- genBranches restLabel discVal (toList branches)
            popBlock
            phi (mkVar Strict) phiNodes
            where
                genBranches :: IR.Label -> Value -> [Alternative] -> Compiler [PhiNode]
                genBranches _ _ [] = do
                    throw 1
                    pure []
                genBranches successLabel var (Alt pattern expr:rest) = do
                    (names, fail) <- unpackPattern (genBranches successLabel var rest) pattern var
                    branchVal <- local (nameMap %~ M.union names) $ codegen expr
                    jump successLabel
                    branchLabel <- blockLabel
                    pure (IR.PhiNode (branchVal, branchLabel) : fromMaybe [] fail)

        codegen (Application fun []) = do
            funVal <- lookupVar fun
            forceCompute funVal

        codegen (Application fun args) = do
            funVal <- lookupVar fun
            forcedFunVal <- forceCompute funVal
            argVals <- forM args $ \case
                Var v -> lookupVar v
                Lit l -> codegen (Literal l)
            call (mkVar Strict) forcedFunVal argVals
                
        codegen (PrimApp fun args) = do
            argVals <- forM args $ \case
                Var v -> lookupVar v
                Lit l -> codegen (Literal l)
            forced <- mapM forceCompute argVals
            let iBuilder = B.functions M.! fun
            B.mkPrim iBuilder (mkVar Strict) argVals

        codegen (ConsApp {}) = undefined

        codegen (Literal lit) = genLiteral lit
            where
                genLiteral :: PrimitiveLiteral -> Compiler Value
                genLiteral (IntLiteral i) = pure (mkInt i)
                genLiteral (RealLiteral r) = pure (IR.ValImmediate (IR.Real64 r))

        codegen (PackedTuple vs) = do
            let tupleType = IR.Structure (map IR.datatype vs)
            tuplePtr <- malloc (mkVar Strict) tupleType
            zipWithM_ (writeVal tuplePtr) vs [0..]
            pure tuplePtr
            where
                getValue :: Atom -> Compiler Value
                getValue (Var v) = lookupVar v
                getValue (Lit l) = codegen (Literal l)

                writeVal :: Value -> Atom -> Int -> Compiler ()
                writeVal base atom offset = do
                    elemPtr <- getElementPtr (mkVar Strict) base [offset]
                    val <- getValue atom
                    write val elemPtr

        codegen (Projector offset v) = do
            let elemType = varType v
            base <- lookupVar v
            forced <- forceCompute base
            addr <- getElementPtr (mkVar Strict) forced [offset]
            read (mkVar Strict) addr

        codegen (Free var expr) = do
            freeVar <- lookupVar var
            addInstruction $ IR.Free freeVar
            codegen expr

        lookupVar :: Var -> Compiler Value
        lookupVar v = do
            strictRecVars <- asks (^. recursiveStrict)
            if S.member v strictRecVars
               then do
                   popBlock
                   pushBlock
                   loop <- blockLabel
                   jump loop
                   popBlock
                   pushBlock
                   pure (IR.ValImmediate IR.Undef)
               else asks ((M.! varID v) . (^. nameMap))

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

        unpackPattern :: Compiler a -> Pattern -> Value -> Compiler (NameMap, Maybe a)
        unpackPattern onFail pattern v = do
            (nameMap, canFail) <- unpack pattern v
            if canFail
               then do
                   pushBlock
                   failResult <- onFail
                   popBlock
                   pure (nameMap, Just failResult)
               else pure (nameMap, Nothing)
            where
                unpack :: Pattern -> Value -> Compiler (NameMap, Bool)
                unpack (VarPattern name) var =
                    pure (M.singleton (varID name) var, False)
                unpack (ConsPattern _ cons args) var = undefined
                unpack (TuplePattern ts) var = do
                    (nameMaps, refutable) <- unzip <$> zipWithM unpackElem ts [0..]
                    pure (M.unions nameMaps, or refutable)
                    where
                        unpackElem :: Pattern -> Int -> Compiler (NameMap, Bool)
                        unpackElem pat index = do
                            elemPtr <- getElementPtr (mkVar Strict) var [index]
                            elem <- read (mkVar Strict) elemPtr
                            unpack pat elem
                unpack (LitPattern lit) var = unpackLit lit
                    where
                        unpackLit :: PrimitiveLiteral -> Compiler (NameMap, Bool)
                        unpackLit (IntLiteral i) =
                            (, True) <$> literalMatcher (mkInt i)
                        unpackLit (RealLiteral r) =
                            (, True) <$> literalMatcher (IR.ValImmediate (IR.Real64 r))

                        literalMatcher :: Value -> Compiler NameMap
                        literalMatcher checkValue = do
                            -- Entry:
                            --  ... | entry
                            -- First, push the "rest" block:
                            --  ... | entry | rest
                            pushBlock
                            restLabel <- blockLabel

                            -- Now, swap so entry is on top:
                            --  ... | rest | entry
                            swapBlocks
                            cmp <- binop IR.Equal (mkVar Strict) var checkValue
                            branch cmp restLabel

                            -- Then, pop the entry block:
                            --  ... | rest
                            popBlock

                            -- We don't bind any vars in a literal pattern
                            pure M.empty

        createFreshThunk :: Maybe AST.Identifier -> [Variable] -> Compiler IR.FunctionID
        createFreshThunk = addFunctionToStack thunkNames

        pushFunction :: Maybe AST.Identifier -> [Variable] -> Compiler IR.FunctionID
        pushFunction = addFunctionToStack functionNames

        addFunctionToStack :: Lens' CompileState (Stream.Stream IR.FunctionID) -> Maybe AST.Identifier
                           -> [Variable]
                           -> Compiler IR.FunctionID
        addFunctionToStack nameSource name args = do
            funcName <- maybe (popName nameSource) extractName name
            let func = IR.makeFunc funcName args
            modify (funcStack %~ (func:))
            pure funcName
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
    
        evaluation :: Value -> Evaluation
        evaluation (IR.ValVariable _ (Variable eval _)) = eval
        evaluation (IR.ValVariable _ (Argument eval _)) = eval
        evaluation _ = Strict

        startState :: CompileState
        startState = CompileState 
            { _blockStack = []
            , _funcStack = []
            , _compiledProgram = IR.addStruct B.thunkTagStruct IR.emptyProgram
            , _labelIDs = Stream.iterate (+1) 0
            , _functionNames = fmap (\f -> IR.FID ("__anonymous_" ++ show f)) (Stream.iterate (+1) 0)
            , _thunkNames = fmap (\f -> IR.FID ("__thunk_" ++ show f)) (Stream.iterate (+1) 0)
            , _blockNames = fmap (\b -> IR.Label ("block_" ++ show b)) (Stream.iterate (+1) 0)
            , _variableID = 0
            }

        startInfo :: CompilerInfo
        startInfo = CompilerInfo
            { _nameMap = M.empty
            , _recursiveStrict = S.empty
            }

testEverything2 :: String -> IO ()
testEverything2 s = case typecheck Builtin.Builtin.defaultBuiltins (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (T.showError s tvm e)
                     Right (t, p) -> print (compile t p) 
    where
        fromRight (Right x) = x

testCompile :: String -> Program
testCompile s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck Builtin.Builtin.defaultBuiltins parsed
     in compile typed poset

