{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module Compiler.Compiler where

import Parser.AST (MultiplicityAtom(..), Identifier(..), Literal(..))
import qualified Typing.Types as T
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
import Data.Maybe (catMaybes, fromMaybe)
import Data.Word
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
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

data CodegenExpr
    = Variable T.Type Identifier
    | Application T.Type CodegenExpr [CodegenExpr]
    | PrimApp T.Type Identifier [CodegenExpr]
    | ConsApp T.Type Identifier [CodegenExpr]
    | Lambda T.Type [T.Pattern] CodegenExpr
    | Case T.Type CodegenExpr (NE.NonEmpty (T.Pattern, CodegenExpr))
    | Let T.Type [(T.Multiplicity, T.Pattern, CodegenExpr)] CodegenExpr

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
freeVars :: S.HashSet Identifier -> T.TypedExpr -> M.HashMap Identifier T.Type
freeVars ignore (T.Let _ bindings body) =
    let extractNames (T.TypedLetBinding _ pattern _) = namesInBinding pattern
        allNames = S.union ignore (foldMap extractNames bindings)
        
        bindingFVs (T.TypedLetBinding _ _ binding) = freeVars allNames binding
     in M.union (freeVars allNames body) (foldMap bindingFVs bindings)
freeVars ignore (T.Case _ _ disc branches) = M.union (freeVars ignore disc) (foldMap branchFVs branches)
    where
        branchFVs :: T.TypedCaseBranch -> M.HashMap Identifier T.Type
        branchFVs (T.TypedCaseBranch pattern body) = freeVars (S.union ignore (namesInBinding pattern)) body
freeVars ignore (T.Application _ fun arg) = M.union (freeVars ignore fun) (freeVars ignore arg)
freeVars ignore (T.Lambda _ _ arg body) = freeVars (S.union ignore (namesInBinding arg)) body
freeVars ignore (T.Variable t name)
    | S.member name ignore = M.empty
    | otherwise = M.singleton name t
freeVars ignore (T.Literal _ lit) = litFVs lit
    where
        litFVs :: Literal T.TypedExpr -> M.HashMap Identifier T.Type
        litFVs (IntLiteral _) = M.empty
        litFVs (RealLiteral _) = M.empty
        litFVs (ListLiteral ls) = foldMap (freeVars ignore) ls
        litFVs (TupleLiteral ts) = foldMap (freeVars ignore) ts

namesInBinding :: T.Pattern -> S.HashSet Identifier
namesInBinding (T.VariablePattern _ name) = S.singleton name
namesInBinding (T.ConstructorPattern _ ps) = foldMap namesInBinding ps
namesInBinding (T.LiteralPattern lit) = namesInLiteral lit
    where
        namesInLiteral :: Literal T.Pattern -> S.HashSet Identifier
        namesInLiteral (IntLiteral _) = S.empty
        namesInLiteral (RealLiteral _) = S.empty
        namesInLiteral (ListLiteral ls) = foldMap namesInBinding ls
        namesInLiteral (TupleLiteral ts) = foldMap namesInBinding ts

convertAST :: T.TypedExpr -> CodegenExpr
convertAST (T.Let t bindings body) = undefined
convertAST (T.Case t _ disc branches) = undefined
convertAST (T.Application t fun arg) = undefined
convertAST (T.Lambda t pattern arrow body) = undefined
convertAST (T.Variable t name) = undefined
convertAST (T.Literal t val) = undefined

type Compiler a = ReaderT CompilerInfo (State CompileState) a

compile :: T.TypedExpr -> T.MultiplicityPoset -> CompileState
compile expr poset = execState (runReaderT finalise startInfo) startState
    where
        finalise :: Compiler ()
        finalise = do
            pushFunction (Just (I "main")) []
            pushBlock
            programResult <- codegen expr
            forced <- forceCompute programResult
            addInstruction $ IR.Return (Just forced)
            popBlock
            void popFunction

        codegen :: T.TypedExpr -> Compiler Value
        codegen (T.Let _ bindings body) = do
            boundVars <- M.unions <$> mapM genBinding bindings
            local (nameMap %~ M.union boundVars) $ codegen body
            where
                genBinding :: T.TypedLetBinding -> Compiler NameMap
                genBinding (T.TypedLetBinding mul pattern binding) =
                    if eager mul || isLambda binding
                       then generator
                       else do
                           recs <- asks (^. recursiveBindings)
                           lazy pattern (freeVars recs binding) generator
                    where
                        generator :: Compiler NameMap
                        generator = do
                            let recs = namesInBinding pattern
                            value <- local (recursiveBindings %~ S.union recs) $ codegen binding
                            fst <$> unpackPattern (addInstruction $ IR.Throw 1) pattern value

                        isLambda :: T.TypedExpr -> Bool
                        isLambda (T.Lambda {}) = True
                        isLambda _ = False

        codegen (T.Case _ _ disc branches) = do
            discVal <- codegen disc
            forcedDisc <- forceCompute discVal
            pushBlock
            phiNodes <- genBranches forcedDisc (toList branches)
            popBlock
            result <- Strict <$> newVar
            addInstruction $ IR.Phi result phiNodes
            pure (IR.ValVariable result)
            where
                genBranches :: Value -> [T.TypedCaseBranch] -> Compiler [PhiNode]
                genBranches _ [] = do
                    addInstruction $ IR.Throw 1
                    pure []
                genBranches var (T.TypedCaseBranch pattern expr:rest) = do
                    (names, fail) <- unpackPattern (genBranches var rest) pattern var
                    branchVal <- local (nameMap %~ M.union names) $ codegen expr
                    branchLabel <- blockLabel
                    pure (IR.PhiNode (branchVal, branchLabel) : fromMaybe [] fail)

        codegen (T.Application _ fun arg) = do
            funVal <- codegen fun
            argVal <- codegen arg
            forcedFun <- forceCompute funVal
            let (T.FunctionType _ (T.Arrow mul) _) = T.typeof fun
            args <- if eager mul
                       then (:[]) <$> forceCompute argVal
                       else unpackLazy <$> wrapLazy (sizeof (T.typeof arg)) argVal
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

        codegen expr@(T.Lambda (T.FunctionType from _ _) mul binding body) = do
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

            funName <- pushFunction Nothing (catMaybes [clArg, Just funArg, offsetArg])
            pushBlock

            boundVars <- fst <$> unpackPattern (addInstruction $ IR.Throw 1) binding (IR.ValVariable argVar)
            -- unpackClosure

            result <- local (nameMap %~ M.union boundVars) $ codegen body

            forced <- forceCompute result
            addInstruction $ IR.Return (Just forced)

            popBlock
            popFunction
            pure (IR.ValClosure (IR.Closure funName Nothing))
            where
                closureArg :: M.HashMap Identifier T.Type -> Compiler (Maybe Variable)
                closureArg fvs
                    | M.null fvs = pure Nothing
                    | otherwise = pure (Just (Strict 0))

        codegen (T.Variable _ name) = asks ((M.! name) . (^. nameMap))
        
        codegen (T.Literal _ lit) = genLiteral lit
            where
                genLiteral :: Literal T.TypedExpr -> Compiler Value
                genLiteral (IntLiteral i) = pure (IR.ValImmediate (IR.Int64 i))
                genLiteral (RealLiteral r) = pure (IR.ValImmediate (IR.Real64 r))
                genLiteral (ListLiteral ls) = undefined
                genLiteral (TupleLiteral ts) = undefined

        eager :: T.Multiplicity -> Bool
        eager mul = P.leq mul (T.MAtom Relevant) poset

        lazy :: T.Pattern -> M.HashMap Identifier T.Type -> Compiler NameMap -> Compiler NameMap
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
            pushBlock
            closureVars <- unpackClosure thunkArg fvsList
            -- Now, we run the regular, strict compiler generator for this function.
            -- We have restricted the input to take a generator which returns a mapping
            -- from variables in the pattern to values. This is therefore essentially
            -- a generator for computing each value that the pattern unwraps.
            thunkResult <- local (nameMap %~ M.union closureVars) generator
            variableMap <- writeOutResults thunkReg thunkArg thunkName (M.toList thunkResult)
            addInstruction $ IR.Return Nothing
            popBlock
            -- Now, we pop the top function on the stack. This function is the thunk
            -- generator.
            popFunction
            pure variableMap
            where
                name :: Maybe Identifier
                name = case names of
                         (T.VariablePattern _ n) -> Just n
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

                packClosure :: Variable -> [(Identifier, T.Type)] -> Compiler ()
                packClosure _ [] = pure ()
                packClosure clVar ((name, t):rest) = do
                    let (offset, size) = closureLayout M.! name
                        offsetVal = IR.ValImmediate (IR.Int64 (fromIntegral offset))
                    addressReg <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add addressReg (IR.ValVariable clVar) offsetVal
                    val <- asks ((M.! name) . (^. nameMap))
                    addInstruction $ IR.Write val (IR.ValVariable addressReg) size
                    packClosure clVar rest

                unpackClosure :: Variable -> [(Identifier, T.Type)] -> Compiler NameMap
                unpackClosure _ [] = pure M.empty
                unpackClosure clVar ((name, t):rest) = do
                    let (offset, size) = closureLayout M.! name
                        offsetVal = IR.ValImmediate (IR.Int64 (fromIntegral offset))
                    addressReg <- Strict <$> newVar
                    addInstruction $ IR.Binop IR.Add addressReg (IR.ValVariable clVar) offsetVal
                    valReg <- Strict <$> newVar
                    addInstruction $ IR.Read valReg (IR.ValVariable addressReg) (sizeof t)
                    M.insert name (IR.ValVariable valReg) <$> unpackClosure clVar rest

                computePatternLayout :: Num a => T.Pattern -> State (a, M.HashMap Identifier (a, a)) ()
                computePatternLayout (T.VariablePattern t n) = do
                    let size = sizeof t
                    offset <- gets fst
                    modify (bimap (+size) (M.insert n (offset, size)))
                computePatternLayout (T.ConstructorPattern _ ps) = mapM_ computePatternLayout ps
                computePatternLayout (T.LiteralPattern lit) = computeLit lit
                    where
                        computeLit :: Num a => Literal T.Pattern -> State (a, M.HashMap Identifier (a, a)) ()
                        computeLit (IntLiteral _) = pure ()
                        computeLit (RealLiteral _) = pure ()
                        computeLit (ListLiteral ls) = mapM_ computePatternLayout ls
                        computeLit (TupleLiteral ts) = mapM_ computePatternLayout ts

                computeClosureLayout :: Num a => [(Identifier, T.Type)] -> State (a, M.HashMap Identifier (a, a)) ()
                computeClosureLayout [] = pure ()
                computeClosureLayout ((n, t):rest) = do
                    let size = sizeof t
                    offset <- gets fst
                    modify (bimap (+size) (M.insert n (offset, size)))

        forceCompute :: Value -> Compiler Value
        forceCompute (IR.ValVariable (Lazy _ cl@(IR.ValClosure (IR.Closure _ (Just addr))) offset size)) = do
            -- We start with a block stack which looks like:
            --  ... | entry
            -- So, we begin by editing the entry block, in particular adding code to test this
            -- thunk
            -- Note that we cannot add a branch instruction yet, as we have no target block
            let addrVar = IR.ValVariable addr

            tag <- Strict <$> newVar
            addInstruction $ IR.Read tag addrVar 1
            evaluated <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Equal evaluated (IR.ValVariable tag) (IR.ValImmediate (IR.Int64 1))

            -- entryBlock <- popBlock

            -- Now, we wish to push the "force" block - this is responsible for forcing the
            -- computation:
            --  ... | entry | force
            pushBlock

            addInstruction $ IR.Call Nothing cl [addrVar]

            -- Next, we swap the top blocks. This is to later apply the entry block
            -- before the force block:
            --  ... | force | entry

            swapBlocks

            -- Next, we push the "rest" block. This is the block we wish to be the top of the
            -- stack upon exit. It also is responsible for unpacking the thunk value:
            --  ... | force | entry | rest
            
            pushBlock
            restLabel <- blockLabel

            addressVar <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add addressVar addrVar offset
            computeVar <- Strict <$> newVar
            addInstruction $ IR.Read computeVar (IR.ValVariable addressVar) size

            -- Now, we swap the top blocks to add the branch instruction to the entry block:
            --  ... | force | rest | entry
            -- Note that if we hadn't performed the earlier swap, the entry block would have
            -- been buried now.

            swapBlocks
            
            addInstruction $ IR.Branch (IR.ValVariable evaluated) restLabel

            -- Next, we pop the entry block as it is complete:
            --  ... | force | rest
            
            popBlock
            
            -- Then, we wish to apply the force block, so we first swap, then pop:
            --  ... | rest | force
            --  ... | rest

            swapBlocks
            popBlock

            pure (IR.ValVariable computeVar)
        forceCompute (IR.ValVariable (Lazy _ addr@(IR.ValVariable {}) offset size)) = do
            tag <- Strict <$> newVar
            addInstruction $ IR.Read tag addr 1
            evaluated <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Equal evaluated (IR.ValVariable tag) (mkInt 1)

            pushBlock

            callAddr <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add callAddr addr (mkInt 1)
            call <- Strict <$> newVar
            addInstruction $ IR.Read call (IR.ValVariable callAddr) pointerSize
            addInstruction $ IR.Call Nothing (IR.ValVariable call) [addr]

            swapBlocks
            pushBlock
            
            restLabel <- blockLabel

            addressVar <- Strict <$> newVar
            addInstruction $ IR.Binop IR.Add addressVar addr offset
            computeVar <- Strict <$> newVar
            addInstruction $ IR.Read computeVar (IR.ValVariable addressVar) size

            swapBlocks

            addInstruction $ IR.Branch (IR.ValVariable evaluated) restLabel

            popBlock
            swapBlocks
            popBlock

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
        
        makeClosure :: M.HashMap Identifier T.Type
                    -> Compiler (Maybe Value, Maybe Variable -> Compiler NameMap)
        makeClosure fvs = pure (Nothing, const (pure M.empty))

        unpackPattern :: Compiler a -> T.Pattern -> Value -> Compiler (NameMap, Maybe a)
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
                unpack :: T.Pattern -> Value -> Compiler (NameMap, Bool)
                unpack (T.VariablePattern t name) var = pure (M.singleton name var, False)
                unpack (T.ConstructorPattern cons args) var = undefined
                unpack (T.LiteralPattern lit) var = unpackLit lit >>= (\nm -> pure (nm, True))
                    where
                        unpackLit :: Literal T.Pattern -> Compiler NameMap
                        unpackLit (IntLiteral i) = do
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
                            addInstruction $ IR.Binop IR.Equal cmpVar var (mkInt i)
                            addInstruction $ IR.Branch (IR.ValVariable cmpVar) restLabel

                            -- Then, pop the entry block:
                            --  ... | rest
                            popBlock

                            -- We don't bind any vars in a literal pattern
                            pure M.empty
                        unpackLit (RealLiteral r) = undefined
                        unpackLit (ListLiteral ls) = undefined
                        unpackLit (TupleLiteral ts) = undefined

        createFreshThunk :: Maybe Identifier -> [Variable] -> Compiler IR.FunctionID
        createFreshThunk = addFunctionToStack thunkNames

        pushFunction :: Maybe Identifier -> [Variable] -> Compiler IR.FunctionID
        pushFunction = addFunctionToStack functionNames

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
                     Left (e, tvm) -> putStrLn (T.showError s tvm e)
                     Right (t, p) -> print (compile t p ^. compiledProgram)
    where
        fromRight (Right x) = x

testCompile :: String -> CompileState
testCompile s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck B.defaultBuiltins parsed
     in compile typed poset

