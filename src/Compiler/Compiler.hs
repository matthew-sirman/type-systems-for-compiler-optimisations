{-# LANGUAGE TemplateHaskell, RankNTypes, TupleSections, DeriveGeneric #-}
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

import Compiler.Size
import Compiler.Translate

import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Program as IR

import qualified Builtin.Codegen as B

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Sequence as Seq hiding (zip, unzip)
import Data.Bifunctor (bimap)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Word
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Strict, Lazy)

import GHC.Generics
import Data.Hashable (Hashable)

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
    = Strict Integer
    | Lazy Integer Word64
    | StrictArgument Integer
    | LazyArgument Integer Word64
    deriving (Eq, Generic)

instance Show Variable where
    show (Strict var) = "tmp" ++ show var
    show (Lazy var _) = "lzy" ++ show var
    show (StrictArgument arg) = "arg" ++ show arg
    show (LazyArgument arg _) = "lzy_arg" ++ show arg

instance Hashable Variable

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

type Compiler a = ReaderT CompilerInfo (State CompileState) a

compile :: T.TypedExpr -> T.MultiplicityPoset -> Program
compile expr poset = execState (runReaderT finalise startInfo) startState ^. compiledProgram
    where
        finalise :: Compiler ()
        finalise = do
            pushFunction (Just (AST.I "main")) []
            pushBlock
            programResult <- codegen (convertAST expr poset)
            forced <- forceCompute programResult
            addInstruction $ IR.Return (Just forced)
            popBlock
            void popFunction

        codegen :: CodegenExpr -> Compiler Value
        codegen (Let bindings body) = do
            boundVars <- M.unions <$> mapM genBinding bindings
            local (nameMap %~ M.union boundVars) $ codegen body
            where
                genBinding :: Binding -> Compiler NameMap
                genBinding (LazyBinding name var (Lf captures (Just resSize) [] body)) = do
                    let thunkSize = 1 + labelSize + sum (map varSize captures)
                    thunkReg <- Lazy <$> newVar <*> pure (fromIntegral resSize)
                    let thunkVar = IR.ValVariable thunkReg

                    -- Create the new thunk function - note that this doesn't affect
                    -- the block we are creating at this point, so instructions will
                    -- still be added to the entry block!
                    -- We do this to get the name of thunk.
                    thunkArg <- StrictArgument <$> newVar
                    thunkName <- createFreshThunk name [thunkArg]
                    let thunkNameValue = IR.ValFunction thunkName
                        thunkArgVar = IR.ValVariable thunkArg

                    -- Add an instruction to allocate the memory
                    -- Then write a 0 tag to indicate that the thunk has not
                    -- been evaluated
                    -- Then write the function address
                    addInstruction $ IR.MAlloc thunkReg (mkInt thunkSize)
                    addInstruction $ IR.Write (mkInt 0) thunkVar 1
                    functionAddress <- IR.ValVariable <$> createAddition thunkVar (mkInt 1)
                    addInstruction $ IR.Write thunkNameValue functionAddress labelSize
                    closureWriter <- createAddition functionAddress (mkInt labelSize)

                    -- Write the captured variables into the closure
                    packClosure captures closureWriter

                    ----- THUNK -----

                    -- Now we start to generate the thunk code itself
                    pushBlock

                    -- Unpack the captured variabes from the closure
                    captureStart <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add captureStart thunkArgVar (mkInt (1 + labelSize))
                    closureVars <- unpackClosure captures captureStart

                    -- Now, we run the regular, strict code generator for the body.
                    thunkResult <- local ( (nameMap %~ M.union closureVars)
                                         . (nameMap %~ M.insert (varID var) thunkArgVar)
                                         ) $ codegen body
                    -- Overwrite the thunk
                    addInstruction $ IR.Write (mkInt 1) thunkArgVar 1
                    writebackAddress <- IR.ValVariable <$> createAddition thunkArgVar (mkInt 1)
                    addInstruction $ IR.Write thunkResult writebackAddress (fromIntegral resSize)
                    addInstruction $ IR.Return Nothing
                    popBlock
                    -- Now, we pop the top function on the stack. This function is the thunk
                    -- generator.
                    popFunction
                    pure (M.singleton (varID var) thunkVar)

                genBinding (LazyBinding name var (Lf [] _ args body)) = do
                    argRegs <- mapM makeArgument args
                    let varMap = M.fromList (zip (map (varID . snd) args) (map IR.ValVariable argRegs))
                    func <- pushFunction name argRegs
                    pushBlock
                    result <- local ( (nameMap %~ M.union varMap)
                                    . (nameMap %~ M.insert (varID var) (IR.ValFunction func))
                                    ) $ codegen body
                    addInstruction $ IR.Return (Just result)
                    popBlock
                    popFunction
                    pure (M.singleton (varID var) (IR.ValFunction func))

                genBinding (LazyBinding name var (Lf captures _ args body)) = do
                    let closureSize = labelSize + sum (map varSize captures)
                    clReg <- Strict <$> newVar
                    let clVar = IR.ValVariable clReg

                    clArg <- StrictArgument <$> newVar

                    argRegs <- mapM makeArgument args
                    let varMap = M.fromList (zip (map (varID . snd) args) (map IR.ValVariable argRegs))

                    funcName <- pushFunction name (clArg:argRegs)
                    let funcNameValue = IR.ValFunction funcName
                        clArgVar = IR.ValVariable clArg

                    -- Add an instruction to allocate the memory
                    -- Then write the function address
                    addInstruction $ IR.MAlloc clReg (mkInt closureSize)
                    addInstruction $ IR.Write funcNameValue clVar labelSize
                    closureWriter <- createAddition clVar (mkInt labelSize)

                    -- Write the captured variables into the closure
                    packClosure captures closureWriter
                    
                    -- Now we start to generate the function
                    pushBlock

                    -- Unpack the captured variabes from the closure
                    captureStart <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add captureStart clArgVar (mkInt labelSize)
                    closureVars <- unpackClosure captures captureStart

                    -- Now, we run the regular, strict code generator for the body.
                    result <- local ( (nameMap %~ M.union closureVars . M.union varMap)
                                    . (nameMap %~ M.insert (varID var) clArgVar)
                                    ) $ codegen body
                    addInstruction $ IR.Return (Just result)
                    popBlock
                    popFunction
                    pure (M.singleton (varID var) clVar)

                genBinding (EagerBinding _ _ pat body) = do
                    res <- local (recursiveStrict %~ S.union (namesInPattern pat)) $ codegen body
                    fst <$> unpackPattern (addInstruction $ IR.Throw 1) pat res

                packClosure :: [Var] -> Variable -> Compiler ()
                packClosure [] _ = pure ()
                packClosure [V sz v] out = do
                    val <- asks ((M.! v) . (^. nameMap))
                    addInstruction $ IR.Write val (IR.ValVariable out) (fromIntegral sz)
                packClosure (V sz v:rest) out = do
                    let out' = IR.ValVariable out
                    val <- asks ((M.! v) . (^. nameMap))
                    addInstruction $ IR.Write val out' (fromIntegral sz)
                    next <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add next out' (mkInt sz)
                    packClosure rest next

                unpackClosure :: [Var] -> Variable -> Compiler NameMap
                unpackClosure [] _ = pure M.empty
                unpackClosure [V sz v] clVar = do
                    readLazy <- asks (isValueLazy . (M.! v) . (^. nameMap))
                    valReg <- if readLazy
                                 then Lazy <$> newVar <*> pure (fromIntegral sz)
                                 else Strict <$> newVar
                    addInstruction $ IR.Read valReg (IR.ValVariable clVar) (fromIntegral sz)
                    pure (M.singleton v (IR.ValVariable valReg))
                unpackClosure (V sz v:rest) clVar = do
                    let cl' = IR.ValVariable clVar
                    readLazy <- asks (isValueLazy . (M.! v) . (^. nameMap))
                    valReg <- if readLazy
                                 then Lazy <$> newVar <*> pure (fromIntegral sz)
                                 else Strict <$> newVar
                    addInstruction $ IR.Read valReg cl' (fromIntegral sz)
                    readLazy <- asks (isValueLazy . (M.! v) . (^. nameMap))
                    next <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add next cl' (mkInt sz)
                    M.insert v (IR.ValVariable valReg) <$> unpackClosure rest next

                makeArgument :: (Bool, Var) -> Compiler Variable
                makeArgument (eager, v)
                    | eager = StrictArgument <$> newVar
                    | otherwise = LazyArgument <$> newVar <*> pure (fromIntegral (varSize v))

        codegen (Case disc branches) = do
            discVal <- codegen disc
            forcedDisc <- forceCompute discVal
            pushBlock
            restLabel <- blockLabel
            swapBlocks
            phiNodes <- genBranches restLabel forcedDisc (toList branches)
            popBlock
            case phiNodes of
              [IR.PhiNode (nodeVal, _)] -> pure nodeVal
              _ -> do
                  result <- Strict <$> newVar
                  addInstruction $ IR.Phi result phiNodes
                  pure (IR.ValVariable result)
            where
                genBranches :: IR.Label -> Value -> [Alternative] -> Compiler [PhiNode]
                genBranches _ _ [] = do
                    addInstruction $ IR.Throw 1
                    pure []
                genBranches successLabel var (Alt pattern expr:rest) = do
                    (names, fail) <- unpackPattern (genBranches successLabel var rest) pattern var
                    branchVal <- local (nameMap %~ M.union names) $ codegen expr
                    addInstruction $ IR.Jump successLabel
                    branchLabel <- blockLabel
                    pure (IR.PhiNode (branchVal, branchLabel) : fromMaybe [] fail)

        codegen (Application arity fun args) = do
            funVal <- lookupVar (varID fun)
            argVals <- mapM (lookupVar . varID) args
            resultReg <- Strict <$> newVar
            addInstruction $ IR.Call (Just resultReg) funVal argVals
            pure (IR.ValVariable resultReg)
            -- where
            --     unpackLazy :: Value -> [Value]
            --     unpackLazy (IR.ValVariable (Lazy _ addr offset _)) = [addr, offset]
            --     unpackLazy v = [v]

                -- unpackClosure :: Value -> [Value]
                -- unpackClosure (IR.ValClosure (IR.Closure _ (Just cl))) = [IR.ValVariable cl]
                -- unpackClosure (IR.ValVariable v) = [IR.ValVariable v]
                -- unpackClosure _ = []
                
        codegen (PrimApp fun args) = do
            argVals <- mapM (lookupVar . varID) args
            forced <- mapM forceCompute argVals
            let iBuilder = B.functions M.! fun
            res <- Strict <$> newVar
            addInstruction $ iBuilder res forced
            pure (IR.ValVariable res)

        codegen (ConsApp {}) = undefined

        codegen (Variable name) = lookupVar (varID name)
        
        codegen (Literal lit) = genLiteral lit
            where
                genLiteral :: PrimitiveLiteral -> Compiler Value
                genLiteral (IntLiteral i) = pure (IR.ValImmediate (IR.Int64 i))
                genLiteral (RealLiteral r) = pure (IR.ValImmediate (IR.Real64 r))

        codegen (PackedTuple vs) = do
            let allocSize = sum (map varSize vs)
            tupleReg <- Strict <$> newVar
            addInstruction $ IR.MAlloc tupleReg (mkInt allocSize)
            let tupleVar = IR.ValVariable tupleReg
            writeOutTuple tupleVar vs
            pure tupleVar
            where
                writeOutTuple :: Value -> [Var] -> Compiler ()
                writeOutTuple addr [] = pure ()
                writeOutTuple addr [v] = do
                    val <- lookupVar (varID v)
                    addInstruction $ IR.Write val addr (fromIntegral (varSize v))
                writeOutTuple addr (v:vs) = do
                    val <- lookupVar (varID v)
                    addInstruction $ IR.Write val addr (fromIntegral (varSize v))
                    next <- createAddition addr (mkInt (varSize v))
                    writeOutTuple (IR.ValVariable next) vs

        codegen (Projector offset size v) = do
            base <- lookupVar (varID v)
            forced <- forceCompute base
            addr <- createAddition forced (mkInt offset)
            result <- Strict <$> newVar
            addInstruction $ IR.Read result (IR.ValVariable addr) (fromIntegral size)
            pure (IR.ValVariable result)
        
        lookupVar :: Integer -> Compiler Value
        lookupVar vid = asks ((M.! vid) . (^. nameMap))

        forceCompute :: Value -> Compiler Value
        forceCompute addr@(IR.ValVariable (Lazy _ sz)) = force addr sz
        forceCompute addr@(IR.ValVariable (LazyArgument _ sz)) = force addr sz
        forceCompute v = pure v

        force :: Value -> Word64 -> Compiler Value
        force addr sz = do
            -- We start with the entry block stack like:
            --  ... | entry
            -- We add instructions to start the test to see if the value
            -- has been evaluated
            tag <- Strict <$> newVar
            addInstruction $ IR.Read tag addr 1
            evaluated <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Equal evaluated (IR.ValVariable tag) (mkInt 1)

            -- Get the payload pointer
            payload <- IR.ValVariable <$> createAddition addr (mkInt 1)

            -- Next, we push the "force" block:
            --  ... | entry | force
            pushBlock

            -- Read the call address out of the closure. This is in the payload location
            callTarget <- Strict <$> newVar
            addInstruction $ IR.Read callTarget payload labelSize
            -- Call the thunk
            addInstruction $ IR.Call Nothing (IR.ValVariable callTarget) [addr]

            -- Now, we swap the blocks. This is to avoid the entry block being buried
            -- later on. Then, we push the "rest" block.
            --  ... | force | entry | rest
            swapBlocks
            pushBlock
            
            restLabel <- blockLabel

            -- We now read out the result variable from the payload
            computeVar <- Strict <$> newVar
            addInstruction $ IR.Read computeVar payload sz

            -- Now we swap the top two blocks. This is because we wish to pop the entry
            -- then force blocks.
            --  ... | force | rest | entry
            swapBlocks

            -- Add the branch instruction to skip over the force block in the case that
            -- the thunk has already been forced
            addInstruction $ IR.Branch (IR.ValVariable evaluated) restLabel

            -- Pop, then swap, then pop again to apply the entry then force blocks
            popBlock
            swapBlocks
            popBlock

            pure (IR.ValVariable computeVar)

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
                unpack (ConsPattern cons args) var = undefined
                unpack (LiteralPattern lit) var = unpackLit lit
                    where
                        unpackLit :: AST.Literal Pattern -> Compiler (NameMap, Bool)
                        unpackLit (AST.IntLiteral i) =
                            (, True) <$> literalMatcher (mkInt i)
                        unpackLit (AST.RealLiteral r) =
                            (, True) <$> literalMatcher (IR.ValImmediate (IR.Real64 r))
                        unpackLit (AST.ListLiteral ls) = undefined
                        unpackLit (AST.TupleLiteral ts) = unpackTuple ts var
                            where
                                unpackTuple :: [Pattern] -> Value -> Compiler (NameMap, Bool)
                                unpackTuple [] _ = pure (M.empty, False)
                                unpackTuple [p] addr = do
                                    let pSize = patternSize p
                                    val <- Strict <$> newVar
                                    addInstruction $ IR.Read val addr pSize
                                    unpack p (IR.ValVariable val)
                                unpackTuple (p:ps) addr = do
                                    let pSize = patternSize p
                                    val <- Strict <$> newVar
                                    addInstruction $ IR.Read val addr pSize
                                    (names, refutable) <- unpack p (IR.ValVariable val)
                                    next <- createAddition addr (mkInt pSize)
                                    (names', refutable') <- unpackTuple ps (IR.ValVariable next)
                                    pure (M.union names names', refutable || refutable')

                        patternSize :: Pattern -> Word64
                        patternSize (VarPattern v) = fromIntegral (varSize v)
                        patternSize (ConsPattern _ _) = undefined
                        patternSize (LiteralPattern lit) = litSize lit
                            where
                                litSize :: AST.Literal Pattern -> Word64
                                litSize (AST.IntLiteral _) = int64Size
                                litSize (AST.RealLiteral _) = realSize
                                litSize (AST.ListLiteral _) = undefined
                                litSize (AST.TupleLiteral _) = pointerSize

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
                            cmpVar <- Strict <$> newVar
                            addInstruction $ IR.Binop IR.Equal cmpVar var checkValue
                            addInstruction $ IR.Branch (IR.ValVariable cmpVar) restLabel

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

        addInstruction :: Instruction -> Compiler ()
        addInstruction i = do
            modify (blockStack . ix 0 . IR.iList %~ (:|> i))

        createAddition :: Value -> Value -> Compiler Variable
        createAddition v1 v2 = do
            res <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add res v1 v2
            pure res

        newVar :: Compiler Integer
        newVar = do
            v <- gets (^. variableID)
            modify (variableID %~ (+1))
            pure v

        mkInt :: Integral a => a -> Value
        mkInt = IR.ValImmediate . IR.Int64 . fromIntegral
    
        isValueLazy :: Value -> Bool
        isValueLazy (IR.ValVariable (Lazy {})) = True
        isValueLazy (IR.ValVariable (LazyArgument {})) = True
        isValueLazy _ = False

        startState :: CompileState
        startState = CompileState 
            { _blockStack = []
            , _funcStack = []
            , _compiledProgram = IR.Program []
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

