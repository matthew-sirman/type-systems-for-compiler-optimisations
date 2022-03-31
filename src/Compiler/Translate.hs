{-# LANGUAGE TemplateHaskell, DeriveGeneric, TupleSections #-}
module Compiler.Translate where

import qualified Util.BoundedPoset as P

import qualified Parser.AST as P
    ( Identifier(..)
    , Literal(..)
    , MultiplicityAtom(..)
    )

import qualified Typing.Types as T
import Typing.Types
    ( Multiplicity(..)
    , Arrow(..)
    , typeof
    )

import qualified Builtin.Codegen as B

import qualified IR.DataType as IR

import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Graph

import Control.Monad.State
import Control.Monad.Reader
import Control.Lens

import GHC.Generics (Generic)
import Data.Hashable (Hashable(..))

-- TODO: Remove
import Typing.Checker
import Parser.Parser
import Debug.Trace
import qualified Builtin.Builtin

voidPtr :: IR.DataType
voidPtr = IR.Pointer (IR.FirstOrder IR.Void)

instance IR.DataTypeContainer T.Type where
    datatype (T.Poly _) = voidPtr
    datatype (T.Ground (P.I "Int")) = IR.FirstOrder IR.Int64T
    datatype (T.Ground (P.I "Real")) = IR.FirstOrder IR.Real64T
    datatype (T.FunctionType from _ to) =
        case IR.datatype to of
          IR.FunctionT res args -> IR.FunctionT res (IR.datatype from : args)
          res -> IR.FunctionT res [IR.datatype from]
    datatype (T.TupleType ts) = IR.Structure (map IR.datatype ts)
    datatype _ = error "Not yet implemented!"

instance IR.DataTypeContainer a => IR.DataTypeContainer (P.Literal a) where
    datatype (P.IntLiteral _) = IR.FirstOrder IR.Int64T
    datatype (P.RealLiteral _) = IR.FirstOrder IR.Real64T
    datatype (P.ListLiteral ls) = undefined
    datatype (P.TupleLiteral ts) = IR.Pointer (IR.Structure (map IR.datatype ts))

instance IR.DataTypeContainer T.Pattern where
    datatype (T.VariablePattern t _) = IR.datatype t
    datatype (T.ConstructorPattern _ ts) = IR.Structure (map IR.datatype ts)
    datatype (T.LiteralPattern lit) = IR.datatype lit

newtype Var = V
    { varID :: Integer
    }
    deriving (Eq, Generic)

instance Show Var where
    show (V x) = "$" ++ show x
    -- show (V _ x) = "$" ++ show x

instance Hashable Var -- where
    -- hashWithSalt salt v = hashWithSalt salt (varID v)
    -- hash v = hash (varID v)

data TypedVar = TV
    { baseVar :: Var
    , varType :: IR.DataType
    }
    deriving Eq

instance Show TypedVar where
    show (TV v dt) = "(" ++ show v ++ " : " ++ show dt ++ ")"

instance Hashable TypedVar where
    hashWithSalt salt = hashWithSalt salt . baseVar
    hash = hash . baseVar

instance IR.DataTypeContainer TypedVar where
    datatype = varType

data PrimitiveLiteral
    = IntLiteral Int
    | RealLiteral Double

instance Show PrimitiveLiteral where
    show (IntLiteral i) = show i
    show (RealLiteral r) = show r

instance IR.DataTypeContainer PrimitiveLiteral where
    datatype (IntLiteral _) = IR.FirstOrder IR.Int64T
    datatype (RealLiteral _) = IR.FirstOrder IR.Real64T

data Atom
    = Var Var
    | Lit PrimitiveLiteral

instance Show Atom where
    show (Var v) = show v
    show (Lit lit) = show lit

-- instance IR.DataTypeContainer Atom where
--     datatype (Var v) = IR.datatype v
--     datatype (Lit l) = IR.datatype l

data CodegenExpr
    = Let [Binding] CodegenExpr
    | Case CodegenExpr (NE.NonEmpty Alternative)
    | Application Var [Atom]
    | PrimApp P.Identifier [Atom]
    | ConsApp P.Identifier [Atom]
    | Literal PrimitiveLiteral
    | PackedTuple IR.DataType [Atom]
    | Projector Int Var
    | Free Var CodegenExpr
    -- | Error

instance Show CodegenExpr where
    show (Let bindings body) = "let " ++ intercalate " and " (map show bindings) ++ " in " ++ show body
    show (Case disc branches) = "case " ++ show disc ++ " of " ++ foldMap (('\n' :) . show) branches
    show (Application fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (PrimApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (ConsApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (Literal lit) = show lit
    show (PackedTuple _ vs) = "(" ++ intercalate ", " (map show vs) ++ ")"
    show (Projector i v) = "sel-" ++ show i ++ " " ++ show v
    show (Free v expr) = "free " ++ show v ++ "; (" ++ show expr ++ ")"
    -- show Error = "error"

data Binding
    = LazyBinding (Maybe P.Identifier) TypedVar LambdaForm
    | EagerBinding (Maybe P.Identifier) TypedVar CodegenExpr

instance Show Binding where
    show (LazyBinding (Just (P.I n)) v lf) = show v ++ "[" ++ n ++ "] = " ++ show lf
    show (LazyBinding Nothing v lf) = show v ++ " = " ++ show lf
    show (EagerBinding (Just (P.I n)) v expr) = show v ++ "[" ++ n ++ "] = " ++ show expr
    show (EagerBinding Nothing p expr) = show p ++ " = " ++ show expr

-- data AtomPattern
--     = VarPattern Var
--     | LitPattern PrimitiveLiteral
-- 
-- instance Show AtomPattern where
--     show (VarPattern v) = show v
--     show (LitPattern lit) = show lit
-- 
-- instance IR.DataTypeContainer AtomPattern where
--     datatype (VarPattern v) = IR.datatype v
--     datatype (LitPattern l) = IR.datatype l

data Pattern
    = VarPattern Var
    | LitPattern PrimitiveLiteral
    -- = AtomPattern AtomPattern
    | ConsPattern IR.DataType P.Identifier [Pattern]
    | TuplePattern [Pattern]
    -- | Ignore

instance Show Pattern where
    show (VarPattern v) = show v
    show (LitPattern lit) = show lit
    -- show (AtomPattern p) = show p
    show (ConsPattern _ name ps) = "(" ++ show name ++ concatMap ((' ':) . show) ps ++ ")"
    show (TuplePattern ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
    -- show Ignore = "_"

-- instance IR.DataTypeContainer Pattern where
--     datatype (VarPattern v) = IR.datatype v
--     datatype (LitPattern l) = IR.datatype l
--     -- datatype (AtomPattern a) = IR.datatype a
--     datatype (ConsPattern dt _ _) = dt
--     datatype (TuplePattern ts) = IR.Structure (map IR.datatype ts)
--     -- datatype Ignore = IR.FirstOrder IR.Void

data LambdaForm = Lf [Var] [(Bool, TypedVar)] CodegenExpr

instance Show LambdaForm where
    show (Lf captures args body) = "{" ++ intercalate ", " (map show captures) ++ "} \\{" 
        ++ intercalate ", " (map (show . snd) args) ++ "} -> " ++ show body

data Alternative = Alt Pattern CodegenExpr

instance Show Alternative where
    show (Alt pattern body) = "| " ++ show pattern ++ " -> " ++ show body

-- failAlt :: Alternative
-- failAlt = Alt Ignore Error

type IdMap = M.HashMap P.Identifier Var

data TranslatorContext = TranslatorContext
    { _idMap :: IdMap
    , _bound :: S.HashSet Var
    , _eager :: Bool
    }

makeLenses ''TranslatorContext

newtype TranslatorState = TranslatorState
    { _nextVar :: Integer
    }

makeLenses ''TranslatorState

type Translator a = ReaderT TranslatorContext (State TranslatorState) a

newtype BindingBuilderState = BindingBuilderState
    { _varsBound :: [(TypedVar, P.Identifier)]
    }

makeLenses ''BindingBuilderState

type BindingBuilder a = StateT BindingBuilderState (ReaderT TranslatorContext (State TranslatorState)) a

findFVs :: CodegenExpr -> Translator (S.HashSet Var)
findFVs (Let bindings body) =
    let extractName (LazyBinding _ v _) = S.singleton (baseVar v)
        extractName (EagerBinding _ v _) = S.singleton (baseVar v)
        findBindFVs (LazyBinding _ _ (Lf _ binds e)) =
            local (bound %~ S.union (S.fromList (map (baseVar . snd) binds))) $ findFVs e
        findBindFVs (EagerBinding _ _ e) = findFVs e
        allNames = S.unions (map extractName bindings)
     in local (bound %~ S.union allNames) $ do
        bindingFVs <- mapM findBindFVs bindings
        bodyFVs <- findFVs body
        pure (S.unions (bodyFVs:bindingFVs))
findFVs (Case disc branches) = do
    discFVs <- findFVs disc
    let findBranch (Alt pattern expr) = local (bound %~ S.union (namesInPattern pattern)) $ findFVs expr
    branchFVs <- NE.toList <$> mapM findBranch branches
    pure (S.unions (discFVs:branchFVs))
findFVs (Application fun args) = do
    fnFVs <- checkFV fun
    argFVs <- mapM checkAtom args
    pure (S.unions (fnFVs:argFVs))
findFVs (PrimApp _ args) = S.unions <$> mapM checkAtom args
findFVs (ConsApp _ args) = S.unions <$> mapM checkAtom args
findFVs (Literal lit) = pure S.empty
findFVs (PackedTuple _ ts) = S.unions <$> mapM checkAtom ts
findFVs (Projector _ v) = checkFV v
findFVs (Free _ expr) = findFVs expr

checkAtom :: Atom -> Translator (S.HashSet Var)
checkAtom (Var v) = checkFV v
checkAtom _ = pure S.empty

checkFV :: Var -> Translator (S.HashSet Var)
checkFV v = do
    isBound <- asks (S.member v . (^. bound))
    if isBound
       then pure S.empty
       else pure (S.singleton v)

-- namesInAtom :: AtomPattern -> S.HashSet Var
-- namesInAtom (VarPattern v) = S.singleton v
-- namesInAtom _ = S.empty

namesInPattern :: Pattern -> S.HashSet Var
namesInPattern (VarPattern v) = S.singleton v
namesInPattern (LitPattern _) = S.empty
-- namesInPattern (AtomPattern atom) = namesInAtom atom
namesInPattern (ConsPattern _ _ ps) = S.unions (map namesInPattern ps)
namesInPattern (TuplePattern ts) = S.unions (map namesInPattern ts)

thunkFunc :: [IR.DataType] -> IR.DataType
thunkFunc args = IR.FunctionT (IR.FirstOrder IR.Void) (thunkArg : args)
    where
        thunkArg :: IR.DataType
        thunkArg = IR.Pointer (IR.Structure [IR.NamedStruct B.thunkTagStruct, voidPtr])

convertAST :: T.TypedExpr -> T.MultiplicityPoset -> CodegenExpr
convertAST expr poset =
    let initCtx = TranslatorContext
            { _idMap = M.empty
            , _bound = S.empty
            , _eager = True
            }
        initState = TranslatorState
            { _nextVar = 0
            }
     in evalState (runReaderT (convert expr) initCtx) initState
    where
        convert :: T.TypedExpr -> Translator CodegenExpr
        convert (T.Let _ bindings body) = do
            (primaryBindings, projectors, names) <- unzip3 <$> mapM createBind bindings
            let allBoundNames = M.unions names
            local (idMap %~ M.union allBoundNames) $ do
                primary <- zipWithM (\bind nms ->
                    local (bound %~ S.union (S.fromList (M.elems nms))) bind) primaryBindings names
                let allBindings = primary ++ concat projectors
                graph <- buildOrderGraph allBindings
                cvtBody <- convert body
                pure (buildLetPath cvtBody (stronglyConnComp graph))
            where
                createBind :: T.TypedLetBinding
                           -> Translator (Translator Binding, [Binding], IdMap)
                createBind (T.TypedLetBinding mul (T.VariablePattern t name) expr) = do
                    bindVar <- freshName
                    let bindTVar = TV bindVar (IR.datatype t)
                        bind = if isEager mul
                                  then EagerBinding (Just name) bindTVar <$>
                                           local (eager .~ True) (convert expr)
                                  else LazyBinding (Just name) bindTVar <$>
                                           local (eager .~ False) (convertLambdas expr)
                    pure (bind, [], M.singleton name bindVar)
                createBind (T.TypedLetBinding mul pat@(T.LiteralPattern (P.TupleLiteral ts)) expr)
                    | all isVarPattern ts = do
                        bindVar <- freshName
                        vars <- mapM (const freshName) ts
                        let bindTVar = TV bindVar (IR.datatype pat)
                            bind = if isEager mul
                                      then EagerBinding Nothing bindTVar <$>
                                               local (eager .~ True) (convert expr)
                                      else LazyBinding Nothing bindTVar <$>
                                               local (eager .~ False) (convertLambdas expr)
                        (ids, projectors) <- unzip <$> zipWithM (makeProjectorBinding bindVar) [0..] ts
                        pure (bind, projectors, M.fromList ids)
                    where
                        makeProjectorBinding :: Var -> Int -> T.Pattern
                                             -> Translator ((P.Identifier, Var), Binding)
                        makeProjectorBinding capture index (T.VariablePattern t v)
                            | isEager mul = do
                                bind <- freshName
                                let proj = Projector index capture
                                    binding = EagerBinding (Just v) (TV bind (IR.datatype t)) proj
                                pure ((v, bind), binding)
                            | otherwise = do
                                bind <- freshName
                                let proj = Lf [capture] [] (Projector index capture)
                                    binding = LazyBinding (Just v) (TV bind (IR.datatype t)) proj
                                pure ((v, bind), binding)
                createBind (T.TypedLetBinding mul pat expr) = do
                    bindVar <- freshName
                    packedVar <- freshName
                    let initState = BindingBuilderState
                            { _varsBound = []
                            }
                    (unpack, bbs) <- runStateT (reformPattern bindVar pat) initState
                    case bbs ^. varsBound of
                      -- [] -> do
                      --     let pvType = IR.Pointer (IR.Structure [])
                      --         varExtractor = unpack (PackedTuple pvType [])

                      --     pure (makeLetBinding (TV packedVar (wrapType pvType)) bindVar varExtractor, [], M.empty)
                      [(v, name)] -> do
                          let pvType = varType v
                              varExtractor = unpack (Application (baseVar v) [])

                          pure (makeLetBinding (Just name) (TV packedVar pvType) varExtractor, [], M.singleton name packedVar)
                      vs -> do
                          let pvStruct = IR.Structure (map (varType . fst) vs)
                              pvType = IR.Pointer pvStruct
                          nameMap <- mapM createNewVar vs
                          let projBinds = zipWith (createProjBinding packedVar) nameMap [0..]
                              varExtractor = unpack (PackedTuple pvStruct (map (Var . baseVar . fst) vs))

                          pure (makeLetBinding Nothing (TV packedVar pvType) varExtractor, projBinds, M.fromList (map (baseVar <$>) nameMap))
                    where
                        createNewVar :: (TypedVar, P.Identifier) -> Translator (P.Identifier, TypedVar)
                        createNewVar (v, name) = do
                            v' <- freshName
                            pure (name, TV v' (varType v))

                        createProjBinding :: Var -> (P.Identifier, TypedVar) -> Int -> Binding
                        createProjBinding capture (name, bindVar) index
                            | isEager mul = EagerBinding (Just name) bindVar proj
                            | otherwise = LazyBinding (Just name) bindVar (Lf [capture] [] proj)
                            where
                                proj :: CodegenExpr
                                proj = Projector index capture

                        makeLetBinding :: Maybe P.Identifier -> TypedVar -> (CodegenExpr -> CodegenExpr)
                                       -> Translator Binding
                        makeLetBinding name packedVar varExtractor
                            | isEager mul = do
                                cvtExpr <- local (eager .~ True) $ convert expr
                                -- pure (EagerBinding (nameForPattern pat) bindVar (insertExpr varExtractor cvtExpr))
                                pure (EagerBinding name packedVar (varExtractor cvtExpr))
                            | otherwise = do
                                (Lf caps args cvtExpr) <- local (eager .~ False) $ convertLambdas expr
                                let lambdaForm = Lf caps args (varExtractor cvtExpr)
                                pure (LazyBinding name packedVar lambdaForm)

                isVarPattern :: T.Pattern -> Bool
                isVarPattern (T.VariablePattern {}) = True
                isVarPattern _ = False

                reformPattern :: Var -> T.Pattern -> BindingBuilder (CodegenExpr -> CodegenExpr -> CodegenExpr)
                reformPattern bv (T.VariablePattern t v) = do
                    modify (varsBound %~ ((TV bv (IR.datatype t), v):))
                    pure const
                reformPattern bv (T.ConstructorPattern name ps) = undefined
                reformPattern bv (T.LiteralPattern lit) = reformPatternLit lit

                reformPatternLit :: P.Literal T.Pattern
                                 -> BindingBuilder (CodegenExpr -> CodegenExpr -> CodegenExpr)
                reformPatternLit (P.IntLiteral i) = do
                    let pattern = LitPattern (IntLiteral i)
                        match rest disc = Case disc (NE.singleton (Alt pattern rest))
                    pure match
                reformPatternLit (P.RealLiteral r) = do
                    let pattern = LitPattern (RealLiteral r)
                        match rest disc = Case disc (NE.singleton (Alt pattern rest))
                    pure match
                reformPatternLit (P.ListLiteral ls) = undefined
                reformPatternLit (P.TupleLiteral ts) = do
                    tempVars <- lift $ mapM (const freshName) ts
                    subPatCombinators <- zipWithM reformPattern tempVars ts
                    let subMatches = zipWith flip subPatCombinators [Application v [] | v <- tempVars]
                        pattern = TuplePattern (map VarPattern tempVars)
                        match rest disc = Case disc (NE.singleton (Alt pattern (foldr id rest subMatches)))
                    pure match

                createNameMap :: (CodegenExpr, BindingBuilderState) -> Translator IdMap
                createNameMap (_, bb)
                    | null (bb ^. varsBound) = pure M.empty

                buildOrderGraph :: [Binding] -> Translator [(Binding, Integer, [Integer])]
                buildOrderGraph [] = pure []
                buildOrderGraph (bind@(EagerBinding _ v body):bs) = do
                    fvs <- findFVs body
                    let node = (bind, (varID . baseVar) v, map varID (S.toList fvs))
                    (node:) <$> buildOrderGraph bs
                buildOrderGraph (bind@(LazyBinding _ v (Lf caps _ _)):bs) = do
                    let node = (bind, (varID . baseVar) v, map varID caps)
                    (node:) <$> buildOrderGraph bs

                buildLetPath :: CodegenExpr -> [SCC Binding] -> CodegenExpr
                buildLetPath base [] = base
                buildLetPath base (AcyclicSCC v:sccs) = Let [v] (buildLetPath base sccs)
                buildLetPath base (CyclicSCC vs:sccs) = Let vs (buildLetPath base sccs)

                nameForPattern :: T.Pattern -> Maybe P.Identifier
                nameForPattern (T.VariablePattern _ name) = Just name
                nameForPattern _ = Nothing

        convert (T.Case _ mul disc branches) = do
            local (eager .~ isEager mul) $ do
                cvtDisc <- convert disc
                cvtBranches <- mapM cvtBranch branches
                pure (Case cvtDisc cvtBranches)
            where
                cvtBranch :: T.TypedCaseBranch -> Translator Alternative
                cvtBranch (T.TypedCaseBranch pat branch) = do
                    (p, ids) <- convertPattern pat
                    cvtBranch <- local (idMap %~ M.union ids) $ convert branch
                    pure (Alt p cvtBranch)

        convert (T.Application _ fun arg) = do
            let (T.FunctionType _ (T.Arrow mul) _) = typeof fun
            collectArgs fun [(mul, arg)]
            where
                collectArgs :: T.TypedExpr -> [(Multiplicity, T.TypedExpr)] -> Translator CodegenExpr
                collectArgs (T.Application _ f a) args =
                    let (T.FunctionType _ (T.Arrow mul) _) = typeof f
                     in collectArgs f ((mul, a):args)
                collectArgs var@(T.Variable _ name) args
                    | M.member name B.functions = liftArgs args (PrimApp name)
                    | M.member name Builtin.Builtin.constructors = liftArgs args (ConsApp name)
                    | otherwise = do
                        funVar <- asks ((M.! name) . (^. idMap))
                        liftArgs args (Application funVar)
                collectArgs expr args = do
                    funExpr <- convert expr
                    case funExpr of
                      Let binds (Application funVar []) -> do
                          liftArgs args (Let binds . Application funVar)
                      _ -> do
                          let funTy = IR.datatype (typeof expr)
                          funVar <- freshName
                          liftArgs args (Let [EagerBinding Nothing (TV funVar funTy) funExpr] . Application funVar)

                liftArgs :: [(Multiplicity, T.TypedExpr)] -> ([Atom] -> CodegenExpr) -> Translator CodegenExpr
                liftArgs args app = do
                    boundArgs <- forM args $ \(mul, arg) -> do
                        let argTy = IR.datatype (typeof arg)
                        argName <- freshName
                        (Var argName,) <$>
                            if isEager mul
                               then EagerBinding Nothing (TV argName argTy) <$>
                                        local (eager .~ True) (convert arg)
                               else LazyBinding Nothing (TV argName argTy) <$>
                                        local (eager .~ False) (convertLambdas arg)
                    let (argVars, binds) = unzip boundArgs
                    pure (Let binds (app argVars))

        convert lam@(T.Lambda t _ _ _) = do
            let lambdaTy = IR.datatype t
            lambdaName <- freshName
            bind <- LazyBinding Nothing (TV lambdaName lambdaTy) <$> convertLambdas lam
            pure (Let [bind] (Application lambdaName []))

        convert (T.Variable _ name) = do
            vName <- asks ((M.! name) . (^. idMap))
            pure (Application vName [])

        convert (T.Literal _ lit) = convertLit lit
            where
                convertLit :: P.Literal T.TypedExpr -> Translator CodegenExpr
                convertLit (P.IntLiteral i) = pure (Literal (IntLiteral i))
                convertLit (P.RealLiteral r) = pure (Literal (RealLiteral r))
                convertLit (P.ListLiteral ls) = undefined
                    -- makeList ls
                    -- where
                    --     makeList :: [T.TypedExpr] -> Translator CodegenExpr
                    --     makeList [] = pure (ConsApp (P.I "[]") [])
                    --     makeList (e:es) = do
                    --         e' <- cvtAST e
                    --         es' <- makeList es
                    --         pure (ConsApp (P.I "::") [e', es'])
                convertLit (P.TupleLiteral ts) = do
                    eagerTuple <- asks (^. eager)
                    bindings <- forM ts $ \expr -> do
                        nm <- TV <$> freshName <*> pure (IR.datatype (typeof expr))
                        if isLambda expr || not eagerTuple
                           then do
                               (nm,) . LazyBinding Nothing nm <$> convertLambdas expr
                           else do
                               (nm,) . EagerBinding Nothing nm <$> convert expr
                    let (vars, binds) = unzip bindings
                        tuple = PackedTuple (IR.Structure (map varType vars)) (map (Var . baseVar) vars)
                    pure (Let binds tuple)

        convertPattern :: T.Pattern -> Translator (Pattern, IdMap)
        convertPattern (T.VariablePattern t name) = do
            v <- freshName
            pure (VarPattern v, M.singleton name v)
        convertPattern (T.ConstructorPattern name ps) = undefined
        convertPattern (T.LiteralPattern lit) = convertLitPattern lit
            where
                convertLitPattern :: P.Literal T.Pattern -> Translator (Pattern, IdMap)
                convertLitPattern (P.IntLiteral i) = pure (LitPattern (IntLiteral i), M.empty)
                convertLitPattern (P.RealLiteral r) = pure (LitPattern (RealLiteral r), M.empty)
                convertLitPattern (P.ListLiteral ls) = undefined
                convertLitPattern (P.TupleLiteral ts) = do
                    (ps, maps) <- unzip <$> mapM convertPattern ts
                    pure (TuplePattern ps, M.unions maps)

        convertLambdas :: T.TypedExpr -> Translator LambdaForm
        convertLambdas lam@(T.Lambda (T.FunctionType from _ _) mul _ _) = do
            varName <- freshName -- (getTypeFor mul from)
            (vs, expr) <- case lam of
                            T.Lambda _ _ (T.VariablePattern _ name) body -> do
                                local (idMap %~ M.insert name varName) $ collectLambdas' 1 [] body
                            T.Lambda _ mul pattern body -> collectLambdas' 1 [(varName, pattern, mul)] body
            fvs <- local (bound %~ S.union (S.fromList (varName:map (baseVar . snd) vs))) $ findFVs expr
            pure (Lf (S.toList fvs) ((isEager mul, TV varName (IR.datatype from)):vs) expr)
            where
                collectLambdas' :: Int -> [(Var, T.Pattern, Multiplicity)] -> T.TypedExpr
                                -> Translator ([(Bool, TypedVar)], CodegenExpr)
                collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
                    varName <- freshName -- (getTypeFor mul from)
                    (vs, expr) <- local (idMap %~ M.insert name varName) $ collectLambdas' (depth + 1) toMatch body
                    pure ((isEager mul, TV varName (IR.datatype from)):vs, expr)
                collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul pattern body) = do
                    varName <- freshName -- (getTypeFor mul from)
                    (vs, expr) <- collectLambdas' (depth + 1) ((varName, pattern, mul):toMatch) body
                    pure ((isEager mul, TV varName (IR.datatype from)):vs, expr)
                collectLambdas' depth toMatch expr = do
                    base <- buildCases (reverse toMatch)
                    pure ([], base)
                    where
                        buildCases :: [(Var, T.Pattern, Multiplicity)] -> Translator CodegenExpr
                        buildCases [] = local (eager .~ False) $ convert expr
                        buildCases ((v, pat, mul):rest) = do
                            (p, ids) <- convertPattern pat
                            local (idMap .~ ids) $ do
                                baseExpr <- (if isAffine mul then Free v else id) <$> buildCases rest
                                pure (Case (Application v []) (NE.singleton (Alt p baseExpr)))

        convertLambdas expr = do
            expr' <- local (eager .~ False) $ convert expr
            fvs <- findFVs expr'
            pure (Lf (S.toList fvs) [] expr')

        -- cvtAST :: T.TypedExpr -> Translator CodegenExpr
        -- cvtAST (T.Let _ bindings body) = do
        --     newVars <- getAllVars
        --     let added = M.foldr S.insert S.empty newVars

        --     local (idMap %~ M.union newVars) $ do
        --         newBindings <- convertLetBindings bindings
        --         newBody <- cvtAST body
        --         graph <- buildOrderGraph added newBindings
        --         pure (buildLetPath newBody (stronglyConnComp graph))
        --     where

        --         getAllVars :: Translator IdMap
        --         getAllVars = foldM (\vs (p, m) -> addPattern m p vs) M.empty [(p, m) | (T.TypedLetBinding m p _) <- bindings]

        --         convertLetBindings :: [T.TypedLetBinding] -> Translator [Binding]
        --         convertLetBindings [] = pure []
        --         convertLetBindings (T.TypedLetBinding m (T.VariablePattern t name) expr:bs) = do
        --             nm <- asks ((M.! name) . (^. idMap))
        --             binds <- convertLetBindings bs
        --             bind <- local (bound %~ S.insert nm) $
        --                 if isLambda expr || not (isEager m)
        --                    then LazyBinding (Just name) nm <$> collectLambdas expr
        --                    else EagerBinding (Just name) <$> nextVarID <*> pure (VarPattern nm) <*> cvtAST expr
        --             pure (bind:binds)
        --         convertLetBindings (T.TypedLetBinding m pattern expr:bs)
        --             | isEager m = do
        --                 pat <- convertPattern pattern
        --                 expr' <- cvtAST expr
        --                 binds <- convertLetBindings bs
        --                 eagerTag <- nextVarID
        --                 pure (EagerBinding Nothing eagerTag pat expr':binds)
        --             | otherwise = do
        --                 -- Note that we can never pattern match a lambda, so expr cannot
        --                 -- be a lambda here (though it may still be a lambda form if it is lazy!)
        --                 pat <- convertPattern pattern
        --                 let varsInPattern = listVars pat []
        --                 binds <- convertLetBindings bs
        --                 case varsInPattern of
        --                   [] -> pure binds
        --                   _ -> local (bound %~ S.union (S.fromList varsInPattern)) $ do
        --                       let packer = PackedTuple (map Var varsInPattern)
        --                       (Lf clVars fnArgs e) <- collectLambdas expr

        --                       nm <- freshName (IR.Pointer (IR.Structure
        --                                                        [ IR.NamedStruct B.thunkTagStruct
        --                                                        , typeToIRData (typeof expr)
        --                                                        ]))

        --                       let structType = IR.Structure (map varType varsInPattern)
        --                           transform = Case e (NE.singleton (Alt pat packer))
        --                           bind = LazyBinding Nothing nm (Lf clVars fnArgs transform)
        --                           projectors = zipWith makeProjector varsInPattern [0..]

        --                           makeProjector :: Var -> Int -> Binding
        --                           makeProjector v i = LazyBinding Nothing v (Lf [nm] [] (Projector i nm))
        --                       pure (bind:projectors)

        --         buildOrderGraph :: S.HashSet Var -> [Binding] -> Translator [(Binding, Integer, [Integer])]
        --         buildOrderGraph _ [] = pure []
        --         buildOrderGraph mrecs (bind@(EagerBinding _ tag _ body):bs) = do
        --             fvs <- findFVs body
        --             let node = (bind, tag, map varID (S.toList (S.intersection mrecs fvs)))
        --             (node:) <$> buildOrderGraph mrecs bs
        --         buildOrderGraph mrecs (bind@(LazyBinding _ v (Lf caps _ _)):bs) = do
        --             let node = (bind, varID v, [varID n | n <- caps, n `S.member` mrecs])
        --             (node:) <$> buildOrderGraph mrecs bs

        --         buildLetPath :: CodegenExpr -> [SCC Binding] -> CodegenExpr
        --         buildLetPath base [] = base
        --         buildLetPath base (AcyclicSCC v:sccs) = Let [v] (buildLetPath base sccs)
        --         buildLetPath base (CyclicSCC vs:sccs) = Let vs (buildLetPath base sccs)

        -- cvtAST (T.Case _ mul disc branches) = do
        --     disc' <- cvtAST disc
        --     branches' <- mapM convertBranch branches
        --     pure (Case disc' branches')
        --     where
        --         convertBranch :: T.TypedCaseBranch -> Translator Alternative
        --         convertBranch (T.TypedCaseBranch p expr) = do
        --             ids' <- asks (^. idMap) >>= addPattern mul p
        --             local (idMap .~ ids') $ do
        --                 e' <- cvtAST expr
        --                 p' <- convertPattern p
        --                 pure (Alt p' e')

        -- cvtAST (T.Application _ fun arg) = do
        --     let (T.FunctionType _ (T.Arrow mul) _) = typeof fun
        --     collectArgs fun [(mul, arg)]
        --     where
        --         collectArgs :: T.TypedExpr -> [(Multiplicity, T.TypedExpr)] -> Translator CodegenExpr
        --         collectArgs (T.Application _ f a) args =
        --             let (T.FunctionType _ (T.Arrow mul) _) = typeof f
        --              in collectArgs f ((mul, a):args)
        --         collectArgs var@(T.Variable _ name) args
        --             | M.member name B.functions = liftArgs args (PrimApp name)
        --             | M.member name Builtin.Builtin.constructors = liftArgs args (ConsApp name)
        --             | otherwise = do
        --                 funVar <- asks ((M.! name) . (^. idMap))
        --                 liftArgs args (Application funVar)
        --         collectArgs expr args = do
        --             funExpr <- cvtAST expr
        --             case funExpr of
        --               Let binds (Application funVar []) -> do
        --                   liftArgs args (Let binds . Application funVar)
        --               _ -> do
        --                   funVar <- freshName (typeToIRData (typeof expr))
        --                   eagerTag <- nextVarID
        --                   liftArgs args (Let [EagerBinding Nothing eagerTag (VarPattern funVar) funExpr] . Application funVar)

        --         liftArgs :: [(Multiplicity, T.TypedExpr)] -> ([Atom] -> CodegenExpr) -> Translator CodegenExpr
        --         liftArgs args app = do
        --             boundArgs <- forM args $ \(mul, arg) -> do
        --                 argName <- freshName (getTypeFor mul (typeof arg))
        --                 (Var argName,) <$>
        --                     if isEager mul
        --                        then EagerBinding Nothing <$> nextVarID <*> pure (VarPattern argName) <*> cvtAST arg
        --                        else LazyBinding Nothing argName <$> collectLambdas arg
        --             let (argVars, binds) = unzip boundArgs
        --             pure (Let binds (app argVars))

        -- cvtAST lam@(T.Lambda t _ _ _) = do
        --     lambdaName <- freshName (typeToIRData t)
        --     bind <- LazyBinding Nothing lambdaName <$> collectLambdas lam
        --     pure (Let [bind] (Application lambdaName []))

        -- cvtAST (T.Variable t name) = do
        --     vName <- asks ((M.! name) . (^. idMap))
        --     pure (Application vName [])

        -- cvtAST (T.Literal t val) = do
        --     convertLit val
        --     where
        --         convertLit :: P.Literal T.TypedExpr -> Translator CodegenExpr
        --         convertLit (P.IntLiteral i) = pure (Literal (IntLiteral i))
        --         convertLit (P.RealLiteral r) = pure (Literal (RealLiteral r))
        --         convertLit (P.ListLiteral ls) = undefined
        --             -- makeList ls
        --             -- where
        --             --     makeList :: [T.TypedExpr] -> Translator CodegenExpr
        --             --     makeList [] = pure (ConsApp (P.I "[]") [])
        --             --     makeList (e:es) = do
        --             --         e' <- cvtAST e
        --             --         es' <- makeList es
        --             --         pure (ConsApp (P.I "::") [e', es'])
        --         convertLit (P.TupleLiteral ts) = do
        --             bindings <- forM ts $ \expr -> do
        --                 let elemBaseType = typeToIRData (typeof expr)
        --                 if isLambda expr
        --                    then do
        --                        nm <- freshName (IR.Pointer (IR.Structure
        --                                                        [ IR.NamedStruct B.thunkTagStruct
        --                                                        , elemBaseType
        --                                                        ]))
        --                        (nm,) . LazyBinding Nothing nm <$> collectLambdas expr
        --                    else do
        --                        nm <- freshName elemBaseType
        --                        eagerTag <- nextVarID
        --                        (nm,) . EagerBinding Nothing eagerTag (VarPattern nm) <$> cvtAST expr
        --             let tuple = PackedTuple (map (Var . fst) bindings)
        --             pure (Let (map snd bindings) tuple)

        -- listVars :: Pattern -> [Var] -> [Var]
        -- listVars (VarPattern v) vs = v:vs
        -- listVars (ConsPattern _ _ ps) vs = foldr listVars vs ps
        -- listVars (LiteralPattern _ lit) vs = listLitPattern lit
        --     where
        --         listLitPattern :: P.Literal Pattern -> [Var]
        --         listLitPattern (P.ListLiteral ls) = foldr listVars vs ls
        --         listLitPattern (P.TupleLiteral ts) = foldr listVars vs ts
        --         listLitPattern _ = vs 

        -- collectLambdas :: T.TypedExpr -> Translator LambdaForm
        -- collectLambdas lam@(T.Lambda (T.FunctionType from _ _) mul _ _) = do
        --     varName <- freshName (getTypeFor mul from)
        --     (vs, expr) <- case lam of
        --                     T.Lambda _ _ (T.VariablePattern _ name) body ->
        --                         local (idMap %~ M.insert name varName) $ collectLambdas' 1 [] body
        --                     T.Lambda _ mul pattern body -> collectLambdas' 1 [(varName, pattern, mul)] body
        --     fvs <- local (bound %~ S.union (S.fromList (varName:map snd vs))) $ findFVs expr
        --     pure (Lf (S.toList fvs) ((isEager mul, varName):vs) expr)
        --     where
        --         collectLambdas' :: Int -> [(Var, T.Pattern, Multiplicity)] -> T.TypedExpr
        --                         -> Translator ([(Bool, Var)], CodegenExpr)
        --         collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
        --             varName <- freshName (getTypeFor mul from)
        --             (vs, expr) <- local (idMap %~ M.insert name varName) $ collectLambdas' (depth + 1) toMatch body
        --             pure ((isEager mul, varName):vs, expr)
        --         collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul pattern body) = do
        --             varName <- freshName (getTypeFor mul from)
        --             (vs, expr) <- collectLambdas' (depth + 1) ((varName, pattern, mul):toMatch) body
        --             pure ((isEager mul, varName):vs, expr)
        --         collectLambdas' depth toMatch expr = do
        --             base <- buildCases (reverse toMatch)
        --             pure ([], base)
        --             where
        --                 buildCases :: [(Var, T.Pattern, Multiplicity)] -> Translator CodegenExpr
        --                 buildCases [] = cvtAST expr
        --                 buildCases ((v, pat, mul):rest) = do
        --                     ids' <- asks (^. idMap) >>= addPattern mul pat
        --                     local (idMap .~ ids') $ do
        --                         baseExpr <- (if isAffine mul then Free v else id) <$> buildCases rest
        --                         cvtPat <- convertPattern pat
        --                         pure (Case (Application v []) (NE.singleton (Alt cvtPat baseExpr)))

        -- collectLambdas expr = do
        --     expr' <- cvtAST expr
        --     fvs <- findFVs expr'
        --     pure (Lf (S.toList fvs) [] expr')

        -- addPattern :: Multiplicity -> T.Pattern -> IdMap -> Translator IdMap
        -- addPattern mul (T.VariablePattern t name) mp = do
        --     nm <- freshName (getTypeFor mul t)
        --     pure (M.insert name nm mp)
        -- addPattern mul (T.ConstructorPattern name ps) mp = foldM (flip (addPattern mul)) mp ps
        -- addPattern mul (T.LiteralPattern lit) mp = addLitPattern lit
        --     where
        --         addLitPattern :: P.Literal T.Pattern -> Translator IdMap
        --         addLitPattern (P.ListLiteral ls) = foldM (flip (addPattern mul)) mp ls
        --         addLitPattern (P.TupleLiteral ts) = foldM (flip (addPattern mul)) mp ts
        --         addLitPattern _ = pure mp

        -- convertPattern :: T.Pattern -> Translator Pattern
        -- convertPattern (T.VariablePattern t name) = asks (VarPattern . (M.! name) . (^. idMap))
        -- convertPattern (T.ConstructorPattern cons ps) = undefined -- ConsPattern cons <$> mapM convertPattern ps
        -- convertPattern (T.LiteralPattern lit) = convertLitPattern lit
        --     where
        --         convertLitPattern :: P.Literal T.Pattern -> Translator Pattern
        --         convertLitPattern (P.IntLiteral i) =
        --             pure (LiteralPattern (IR.FirstOrder IR.Int64T) (P.IntLiteral i))
        --         convertLitPattern (P.RealLiteral r) =
        --             pure (LiteralPattern (IR.FirstOrder IR.Int64T) (P.RealLiteral r))
        --         convertLitPattern (P.ListLiteral ls) = undefined
        --             -- P.ListLiteral <$> mapM convertPattern ls
        --         convertLitPattern (P.TupleLiteral ts) = do
        --             ps <- mapM convertPattern ts
        --             pure (LiteralPattern (IR.Structure (map patternDataType ps)) (P.TupleLiteral ps))

        isEager :: Multiplicity -> Bool
        isEager mul = P.leq mul (T.MAtom P.Relevant) poset

        isAffine :: Multiplicity -> Bool
        isAffine mul = P.leq mul (T.MAtom P.Affine) poset

        isLambda :: T.TypedExpr -> Bool
        isLambda (T.Lambda {}) = True
        isLambda _ = False

        -- getTypeFor :: T.Multiplicity -> T.Type -> IR.DataType
        -- getTypeFor _ t@(T.FunctionType {}) = IR.datatype t
        -- getTypeFor mul t
        --     | isEager mul = IR.datatype t
        --     | otherwise = IR.Pointer (IR.Structure
        --                                  [ IR.NamedStruct B.thunkTagStruct
        --                                  , IR.datatype t
        --                                  ])

        freshName :: Translator Var
        freshName = do
            v <- gets (^. nextVar)
            modify (nextVar %~ (+1))
            pure (V v)

        -- nextVarID :: Translator Integer
        -- nextVarID = do
        --     v <- gets (^. nextVar)
        --     modify (nextVar %~ (+1))
        --     pure v

testTranslate :: String -> CodegenExpr
testTranslate s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck Builtin.Builtin.defaultBuiltins parsed
     in convertAST typed poset
