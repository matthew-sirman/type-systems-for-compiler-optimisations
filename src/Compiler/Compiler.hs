{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module Compiler.Compiler where

import Parser.AST (MultiplicityAtom(..), Identifier(..), Literal(..))
import Typing.Types
import qualified Util.BoundedPoset as P
import qualified Util.Stream as Stream

import Compiler.Size

import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Program as IR

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Sequence as Seq
import Data.Bifunctor (bimap)
import Data.Maybe (catMaybes)
import Data.Word
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Strict, Lazy)

-- TODO: Remove
import Typing.Checker
import Parser.Parser
import qualified Builtin.Builtin as B
import Debug.Trace

type Value = IR.Value Variable
type Closure = IR.Closure Variable
type Instruction = IR.Instruction Variable
type PhiNode = IR.PhiNode Variable
type BasicBlock = IR.BasicBlock Variable
type Function = IR.Function Variable
type Program = IR.Program Variable

type NameMap = M.HashMap Identifier Value

data Variable
    = Strict Integer
    | Lazy Integer Value Value Word64
    | Argument Integer

instance Show Variable where
    show (Strict var) = "tmp" ++ show var
    show (Lazy var _ _ _) = "lzy" ++ show var
    show (Argument arg) = "arg" ++ show arg

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
    , _recursiveBindings :: S.HashSet Identifier
    }

makeLenses ''CompilerInfo

-- TODO: Think about making a less conservative approach for capturing free vars
-- For example:
-- In the expression
--  \x -> let y = 0 and z = y + 1 in z
-- the thunk computing 'z' does not need to capture 'y'
-- However, in the expression
--  \x -> let y = x + 1 and z = y + 1 in z
-- the thunk for 'z' does need to capture 'y', as 'y' depends on 'x' which is free.
--
-- So, as of now, 'y' is captured conservatively in both cases.
freeVars :: S.HashSet Identifier -> TypedExpr -> M.HashMap Identifier Type
freeVars ignore (Let _ bindings body) =
    let extractNames (TypedLetBinding _ pattern _) = namesInBinding pattern
        allNames = S.union ignore (foldMap extractNames bindings)
        
        bindingFVs (TypedLetBinding _ _ binding) = freeVars allNames binding
     in M.union (freeVars allNames body) (foldMap bindingFVs bindings)
freeVars ignore (Case _ _ disc branches) = M.union (freeVars ignore disc) (foldMap branchFVs branches)
    where
        branchFVs :: TypedCaseBranch -> M.HashMap Identifier Type
        branchFVs (TypedCaseBranch pattern body) = freeVars (S.union ignore (namesInBinding pattern)) body
freeVars ignore (Application _ fun arg) = M.union (freeVars ignore fun) (freeVars ignore arg)
freeVars ignore (Lambda _ _ arg body) = freeVars (S.union ignore (namesInBinding arg)) body
freeVars ignore (Variable t name)
    | S.member name ignore = M.empty
    | otherwise = M.singleton name t
freeVars ignore (Literal _ lit) = litFVs lit
    where
        litFVs :: Literal TypedExpr -> M.HashMap Identifier Type
        litFVs (IntLiteral _) = M.empty
        litFVs (RealLiteral _) = M.empty
        litFVs (ListLiteral ls) = foldMap (freeVars ignore) ls
        litFVs (TupleLiteral ts) = foldMap (freeVars ignore) ts

namesInBinding :: Pattern -> S.HashSet Identifier
namesInBinding (VariablePattern _ name) = S.singleton name
namesInBinding (ConstructorPattern _ ps) = foldMap namesInBinding ps
namesInBinding (LiteralPattern lit) = namesInLiteral lit
    where
        namesInLiteral :: Literal Pattern -> S.HashSet Identifier
        namesInLiteral (IntLiteral _) = S.empty
        namesInLiteral (RealLiteral _) = S.empty
        namesInLiteral (ListLiteral ls) = foldMap namesInBinding ls
        namesInLiteral (TupleLiteral ts) = foldMap namesInBinding ts

type Compiler a = ReaderT CompilerInfo (State CompileState) a

compile :: TypedExpr -> MultiplicityPoset -> CompileState
compile expr poset = execState (runReaderT finalise startInfo) startState
    where
        finalise :: Compiler ()
        finalise = do
            pushFreshFunction (Just (I "main")) []
            createBlock
            programResult <- codegen expr
            forced <- forceCompute programResult
            addInstruction $ IR.Return (Just forced)
            popBlock >>= applyBlock
            void popFunction

        codegen :: TypedExpr -> Compiler Value
        codegen (Let _ bindings body) = do
            boundVars <- M.unions <$> mapM genBinding bindings
            local (nameMap %~ M.union boundVars) $ codegen body
            where
                genBinding :: TypedLetBinding -> Compiler NameMap
                genBinding (TypedLetBinding mul pattern binding) =
                    if eager mul
                       then generator
                       else do
                           recs <- asks (^. recursiveBindings)
                           lazy pattern (freeVars recs binding) generator
                    where
                        generator :: Compiler NameMap
                        generator = do
                            let recs = namesInBinding pattern
                            value <- local (recursiveBindings %~ S.union recs) $ codegen binding
                            unpackPattern (addInstruction $ IR.Throw 1) pattern value

        codegen (Case _ _ disc branches) = do
            discVal <- codegen disc
            forcedDisc <- forceCompute discVal
            -- unpack b1
            -- unpack b2
            pure ()
            pure forcedDisc
            where
                genBranches :: Value -> [TypedCaseBranch] -> Compiler [Value]
                genBranches _ [] = pure []
                genBranches var (TypedCaseBranch pattern expr:rest) = do
                    --  case x of | 0 -> 0 | 1 -> 1 | 2 -> 2
                    --
                    --        tmp0 <- ... generate x ...
                    --        br tmp0 = 0 case0
                    --        br tmp0 = 1 case1
                    --        br tmp0 = 2 case2
                    --        jmp rest
                    -- case0: tmp1 <- 0
                    --        jmp rest
                    -- case1: tmp2 <- 1
                    --        jmp rest
                    -- case2: tmp3 <- 2
                    --        jmp rest
                    --  fail: throw 1
                    --  rest: tmp4 <- phi [ case0 : tmp1, case1 : tmp2, case2: tmp3 ]
                    --
                    -- (names, results) <- unpackPattern (genBranches var rest) pattern var
                    pure []

        codegen (Application _ fun arg) = do
            funVal <- codegen fun
            argVal <- codegen arg
            forcedFun <- forceCompute funVal
            let (FunctionType _ (Arrow mul) _) = typeof fun
            args <- if eager mul
                       then (:[]) <$> forceCompute argVal
                       else unpackLazy <$> wrapLazy (sizeof (typeof arg)) argVal
            resultReg <- Strict <$> newVar
            addInstruction $ IR.Call (Just resultReg) forcedFun (unpackClosure funVal ++ args)
            pure (IR.ValVariable resultReg)
            where
                unpackLazy :: Value -> [Value]
                unpackLazy (IR.ValVariable (Lazy _ addr offset _)) = [addr, offset]
                unpackLazy v = [v]

                unpackClosure :: Value -> [Value]
                unpackClosure (IR.ValClosure (IR.Closure _ (Just cl))) = [IR.ValVariable cl]
                unpackClosure (IR.ValVariable v) = [IR.ValVariable v]
                unpackClosure _ = []

        codegen expr@(Lambda (FunctionType from _ _) mul binding body) = do
            recs <- asks (^. recursiveBindings)
            let fvs = freeVars recs expr

            clArg <- closureArg fvs

            funArg <- Argument <$> newVar
            (offsetArg, argVar) <- if eager mul
                                      then pure (Nothing, funArg)
                                      else do
                                          offArg <- Argument <$> newVar
                                          lazyArg <- newVar
                                          let fArgV = IR.ValVariable funArg
                                              oArgV = IR.ValVariable offArg
                                          pure (Just offArg, Lazy lazyArg fArgV oArgV (sizeof from))

            funName <- pushFreshFunction Nothing (catMaybes [clArg, Just funArg, offsetArg])
            createBlock

            boundVars <- unpackPattern (addInstruction $ IR.Throw 1) binding (IR.ValVariable argVar)
            -- unpackClosure

            result <- local (nameMap %~ M.union boundVars) $ codegen body

            forced <- forceCompute result
            addInstruction $ IR.Return (Just forced)

            popBlock >>= applyBlock
            popFunction
            pure (IR.ValClosure (IR.Closure funName Nothing))
            where
                closureArg :: M.HashMap Identifier Type -> Compiler (Maybe Variable)
                closureArg fvs
                    | M.null fvs = pure Nothing
                    | otherwise = pure (Just (Strict 0))

        codegen (Variable _ name) = asks ((M.! name) . (^. nameMap))
        
        codegen (Literal _ lit) = genLiteral lit
            where
                genLiteral :: Literal TypedExpr -> Compiler Value
                genLiteral (IntLiteral i) = pure (IR.ValImmediate (IR.Int64 i))
                genLiteral (RealLiteral r) = pure (IR.ValImmediate (IR.Real64 r))
                genLiteral (ListLiteral ls) = undefined
                genLiteral (TupleLiteral ts) = undefined

        eager :: Multiplicity -> Bool
        eager mul = P.leq mul (MAtom Relevant) poset

        lazy :: Pattern -> M.HashMap Identifier Type -> Compiler NameMap -> Compiler NameMap
        lazy names fvs generator = do
            let fvsList = M.toList fvs
            -- First, we need to allocate memory for the thunk. This will comprise of
            --    - a single byte which will be used to determine whether the value
            --      has already been computer or not. This way, we don't recompute
            --      values
            --    - enough space for each of the types which will be generated based
            --      on the pattern being generated for. E.g., if we have the pattern
            --      "(x, y)", we need to allocate space for the size of "x" and for "y".
            thunkReg <- Strict <$> newVar
            -- Add an instruction to allocate the memory
            addInstruction $ IR.MAlloc thunkReg (mkInt (fromIntegral totalClosureSize))
            addInstruction $ IR.Write (IR.ValImmediate (IR.Int64 0)) (IR.ValVariable thunkReg) 1

            packClosure thunkReg fvsList

            thunkArg <- Argument <$> newVar
            -- Next, we create a new function. This will compute the thunk values when it is
            -- first invoked.
            thunkName <- createFreshThunk name [thunkArg]
            createBlock
            closureVars <- unpackClosure thunkArg fvsList
            -- Now, we run the regular, strict compiler generator for this function.
            -- We have restricted the input to take a generator which returns a mapping
            -- from variables in the pattern to values. This is therefore essentially
            -- a generator for computing each value that the pattern unwraps.
            thunkResult <- local (nameMap %~ M.union closureVars) generator
            variableMap <- writeOutResults thunkReg thunkArg thunkName (M.toList thunkResult)
            addInstruction $ IR.Return Nothing
            popBlock >>= applyBlock
            -- Now, we pop the top function on the stack. This function is the thunk
            -- generator.
            popFunction
            pure variableMap
            where
                name :: Maybe Identifier
                name = case names of
                         (VariablePattern _ n) -> Just n
                         _ -> Nothing

                (totalPatternSize, patternLayout) =
                    execState (computePatternLayout names) (1, M.empty)
                (totalClosureSize, closureLayout) =
                    execState (computeClosureLayout (M.toList fvs)) (totalPatternSize, M.empty)

                writeOutResults :: Variable -> Variable -> IR.FunctionID -> [(Identifier, Value)]
                                -> Compiler NameMap
                writeOutResults clVar baseAddress thunkName valMap = do
                    nameMap <- write valMap
                    addInstruction $ IR.Write (mkInt 1) (IR.ValVariable baseAddress) 1
                    pure nameMap
                    where
                        closure :: Closure
                        closure = IR.Closure thunkName (Just clVar)

                        write :: [(Identifier, Value)] -> Compiler NameMap
                        write [] = pure M.empty
                        write ((name, val):rest) = do
                            let (offset, size) = patternLayout M.! name
                                offsetVal = mkInt (fromIntegral offset)
                            addressReg <- Strict <$> newVar
                            addInstruction $ IR.Binop IR.Add addressReg (IR.ValVariable baseAddress) offsetVal
                            -- TODO: This may need to do a copy rather than write
                            addInstruction $ IR.Write val (IR.ValVariable addressReg) size
                            lazyVarName <- newVar
                            let addressVar = IR.ValVariable addressReg
                                lazyVar = IR.ValVariable (Lazy lazyVarName (IR.ValClosure closure) (mkInt (fromIntegral offset)) size)
                            M.insert name lazyVar <$> write rest

                packClosure :: Variable -> [(Identifier, Type)] -> Compiler ()
                packClosure _ [] = pure ()
                packClosure clVar ((name, t):rest) = do
                    let (offset, size) = closureLayout M.! name
                        offsetVal = IR.ValImmediate (IR.Int64 (fromIntegral offset))
                    addressReg <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add addressReg (IR.ValVariable clVar) offsetVal
                    val <- asks ((M.! name) . (^. nameMap))
                    addInstruction $ IR.Write val (IR.ValVariable addressReg) size
                    packClosure clVar rest

                unpackClosure :: Variable -> [(Identifier, Type)] -> Compiler NameMap
                unpackClosure _ [] = pure M.empty
                unpackClosure clVar ((name, t):rest) = do
                    let (offset, size) = closureLayout M.! name
                        offsetVal = IR.ValImmediate (IR.Int64 (fromIntegral offset))
                    addressReg <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add addressReg (IR.ValVariable clVar) offsetVal
                    valReg <- Strict <$> newVar
                    addInstruction $ IR.Read valReg (IR.ValVariable addressReg) (sizeof t)
                    M.insert name (IR.ValVariable valReg) <$> unpackClosure clVar rest

                computePatternLayout :: Num a => Pattern -> State (a, M.HashMap Identifier (a, a)) ()
                computePatternLayout (VariablePattern t n) = do
                    let size = sizeof t
                    offset <- gets fst
                    modify (bimap (+size) (M.insert n (offset, size)))
                computePatternLayout (ConstructorPattern _ ps) = mapM_ computePatternLayout ps
                computePatternLayout (LiteralPattern lit) = computeLit lit
                    where
                        computeLit :: Num a => Literal Pattern -> State (a, M.HashMap Identifier (a, a)) ()
                        computeLit (IntLiteral _) = pure ()
                        computeLit (RealLiteral _) = pure ()
                        computeLit (ListLiteral ls) = mapM_ computePatternLayout ls
                        computeLit (TupleLiteral ts) = mapM_ computePatternLayout ts

                computeClosureLayout :: Num a => [(Identifier, Type)] -> State (a, M.HashMap Identifier (a, a)) ()
                computeClosureLayout [] = pure ()
                computeClosureLayout ((n, t):rest) = do
                    let size = sizeof t
                    offset <- gets fst
                    modify (bimap (+size) (M.insert n (offset, size)))

        forceCompute :: Value -> Compiler Value
        forceCompute (IR.ValVariable (Lazy _ cl@(IR.ValClosure (IR.Closure _ (Just addr))) offset size)) = do
            let addrVar = IR.ValVariable addr

            tag <- Strict <$> newVar
            addInstruction $ IR.Read tag addrVar 1
            evaluated <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Equal evaluated (IR.ValVariable tag) (IR.ValImmediate (IR.Int64 1))

            entryBlock <- popBlock

            createBlock

            addInstruction $ IR.Call Nothing cl [addrVar]

            forceBlock <- popBlock

            createBlock
            restLabel <- blockLabel

            addressVar <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add addressVar addrVar offset
            computeVar <- Strict <$> newVar
            addInstruction $ IR.Read computeVar (IR.ValVariable addressVar) size

            let branchInstruction = IR.Branch (IR.ValVariable evaluated) restLabel
            applyBlock $ IR.blockPush branchInstruction entryBlock
            applyBlock forceBlock

            pure (IR.ValVariable computeVar)
        forceCompute (IR.ValVariable (Lazy _ addr@(IR.ValVariable {}) offset size)) = do
            tag <- Strict <$> newVar
            addInstruction $ IR.Read tag addr 1
            evaluated <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Equal evaluated (IR.ValVariable tag) (mkInt 1)

            entryBlock <- popBlock

            createBlock

            callAddr <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add callAddr addr (mkInt 1)
            call <- Strict <$> newVar
            addInstruction $ IR.Read call (IR.ValVariable callAddr) pointerSize
            addInstruction $ IR.Call Nothing (IR.ValVariable call) [addr]

            forceBlock <- popBlock

            createBlock
            restLabel <- blockLabel

            addressVar <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add addressVar addr offset
            computeVar <- Strict <$> newVar
            addInstruction $ IR.Read computeVar (IR.ValVariable addressVar) size

            let branchInstruction = IR.Branch (IR.ValVariable evaluated) restLabel
            applyBlock $ IR.blockPush branchInstruction entryBlock
            applyBlock forceBlock

            pure (IR.ValVariable computeVar)
        forceCompute (IR.ValVariable (Lazy _ imm _ _)) = pure imm
        forceCompute v = pure v

        wrapLazy :: Word64 -> Value -> Compiler Value
        wrapLazy _ v@(IR.ValVariable (Lazy {})) = pure v
        wrapLazy _ v@(IR.ValClosure _) = pure v
        wrapLazy size imm = do
            baseAddress <- Strict <$> newVar
            addInstruction $ IR.MAlloc baseAddress (mkInt (fromIntegral (1 + size)))
            addInstruction $ IR.Write (mkInt 1) (IR.ValVariable baseAddress) 1
            valAddress <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add valAddress (IR.ValVariable baseAddress) (mkInt 1)
            addInstruction $ IR.Write imm (IR.ValVariable valAddress) size
            lazyVar <- newVar
            pure (IR.ValVariable (Lazy lazyVar (IR.ValVariable baseAddress) (mkInt 1) size))
        
        makeClosure :: M.HashMap Identifier Type
                    -> Compiler (Maybe Value, Maybe Variable -> Compiler NameMap)
        makeClosure fvs = pure (Nothing, const (pure M.empty))

        unpackPattern :: Compiler () -> Pattern -> Value -> Compiler NameMap
        unpackPattern _ (VariablePattern t name) var = pure (M.singleton name var)
        unpackPattern onFail (ConstructorPattern cons args) var = undefined
        unpackPattern onFail (LiteralPattern lit) var = unpackLit lit
            where
                unpackLit :: Literal Pattern -> Compiler NameMap
                unpackLit (IntLiteral i) = do
                    createBlock
                    failResult <- onFail
                    failBlock <- popBlock
                    cmpVar <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Equal cmpVar var (mkInt i)
                    entryBlock <- popBlock
                    createBlock
                    restLabel <- blockLabel
                    let branchInstruction = IR.Branch (IR.ValVariable cmpVar) restLabel
                    applyBlock $ IR.blockPush branchInstruction entryBlock
                    applyBlock failBlock
                    pure M.empty
                unpackLit (RealLiteral r) = undefined
                unpackLit (ListLiteral ls) = undefined
                unpackLit (TupleLiteral ts) = undefined

        createFreshThunk :: Maybe Identifier -> [Variable] -> Compiler IR.FunctionID
        createFreshThunk = addFunctionToStack thunkNames

        pushFreshFunction :: Maybe Identifier -> [Variable] -> Compiler IR.FunctionID
        pushFreshFunction = addFunctionToStack functionNames

        addFunctionToStack :: Lens' CompileState (Stream.Stream IR.FunctionID) -> Maybe Identifier
                           -> [Variable]
                           -> Compiler IR.FunctionID
        addFunctionToStack nameSource name args = do
            funcName <- getFuncName
            let func = IR.makeFunc funcName args
            modify (funcStack %~ (func:))
            pure funcName
            where
                getFuncName :: Compiler IR.FunctionID
                getFuncName = case name of
                                Just (I n) -> pure (IR.FID n)
                                Nothing -> popName nameSource

        popFunction :: Compiler Function
        popFunction = do
            (fn, rest) <- gets (uncons . (^. funcStack))
            modify (funcStack .~ rest)
            modify (compiledProgram %~ IR.addFunction fn)
            pure fn
            where
                uncons :: [a] -> (a, [a])
                uncons (x:xs) = (x, xs)

        createBlock :: Compiler ()
        createBlock = do
            blockId <- popName blockNames
            let block = IR.makeBasicBlock blockId
            modify (blockStack %~ (block:))

        popBlock :: Compiler BasicBlock
        popBlock = do
            (blk, rest) <- gets (uncons . (^. blockStack))
            modify (blockStack .~ rest)
            pure blk
            where
                uncons :: [a] -> (a, [a])
                uncons (x:xs) = (x, xs)

        applyBlock :: BasicBlock -> Compiler ()
        applyBlock blk = do
            modify (funcStack . ix 0 . IR.blocks %~ (:|> blk))

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

        newVar :: Compiler Integer
        newVar = do
            v <- gets (^. variableID)
            modify (variableID %~ (+1))
            pure v

        mkInt :: Int -> Value
        mkInt = IR.ValImmediate . IR.Int64

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
            , _recursiveBindings = S.empty
            }

testEverything2 :: String -> IO ()
testEverything2 s = case typecheck B.defaultBuiltins (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (showError s tvm e)
                     Right (t, p) -> print (compile t p ^. compiledProgram)
    where
        fromRight (Right x) = x

testCompile :: String -> CompileState
testCompile s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck B.defaultBuiltins parsed
     in compile typed poset

