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

import Builtin.Codegen as B

-- import qualified IR.DataType as IR

import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import Data.Maybe (catMaybes, fromJust, isJust)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Graph

import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Strict, Lazy)

import GHC.Generics (Generic)
import Data.Hashable (Hashable(..))

-- TODO: Remove
import Typing.Checker
import Parser.Parser
import Debug.Trace
import qualified Builtin.Builtin

data Evaluation
    = Strict
    | Lazy
    deriving (Eq, Generic, Show)

instance Hashable Evaluation

class TranslateTyped a where
    ttype :: a -> TranslateType

data TranslateType
    = IntT
    | RealT
    | Poly Integer
    | Tuple [TranslateType]
    | Named P.Identifier
    | TypeApp P.Identifier [TranslateType]
    | Function TranslateType [TranslateType]
    | Boxed TranslateType
    deriving Eq

instance Show TranslateType where
    show IntT = "int"
    show RealT = "real"
    show (Poly i) = "p" ++ show i
    show (Tuple ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
    show (Named name) = show name
    show (TypeApp base args) = show base ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (Function res args) = show res ++ " (" ++ intercalate ", " (map show args) ++ ")"
    show (Boxed t) = "[" ++ show t ++ "]"

weakNormal :: TranslateType -> TranslateType
weakNormal (Boxed t) = t
weakNormal t = t

headNormal :: TranslateType -> TranslateType
headNormal (Tuple ts) = Tuple (map headNormal ts)
headNormal (Boxed t) = headNormal t
headNormal t = t

isBoxed :: TranslateType -> Bool
isBoxed (Boxed _) = True
isBoxed _ = False

instance TranslateTyped T.Type where
    ttype (T.Poly p) = Boxed (Poly p)
    ttype (T.Ground (P.I "Int#")) = IntT
    ttype (T.Ground (P.I "Real#")) = RealT
    ttype (T.Ground name) = Boxed (Named name)
    ttype (T.FunctionType from _ to) =
        case ttype to of
          Function res args -> Function res (ttype from : args)
          res -> Function (weakNormal res) [ttype from]
    ttype (T.TupleType ts) = Boxed (Tuple (map ttype ts))
    ttype (T.TypeApp head arg) =
        case ttype head of
          TypeApp base args -> TypeApp base (weakNormal (ttype arg) : args)
          Boxed (TypeApp base args) -> Boxed (TypeApp base (weakNormal (ttype arg) : args))
          Named name -> TypeApp name [weakNormal (ttype arg)]
          Boxed (Named name) -> Boxed (TypeApp name [weakNormal (ttype arg)])
          t -> error (show t)

-- instance TranslateTyped a => TranslateTyped (P.Literal a) where
--     ttype (P.IntLiteral _) = IntT
--     ttype (P.RealLiteral _) = RealT
--     ttype (P.ListLiteral _) = Named (P.I "[]")
--     ttype (P.TupleLiteral ts) = Tuple (map ttype ts)

-- instance TranslateTyped T.Pattern where
--     ttype (T.VariablePattern t _) = ttype t
--     ttype (T.ConstructorPattern _ ts) = undefined
--     ttype (T.LiteralPattern lit) = ttype lit
-- 
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
    , varType :: TranslateType
    }
    deriving Eq

instance Show TypedVar where
    show (TV v dt) = "(" ++ show v ++ " : " ++ show dt ++ ")"

instance Hashable TypedVar where
    hashWithSalt salt = hashWithSalt salt . baseVar
    hash = hash . baseVar

-- instance IR.DataTypeContainer TypedVar where
--     datatype = varType

data PrimitiveLiteral
    = IntLiteral Int
    | RealLiteral Double

instance Show PrimitiveLiteral where
    show (IntLiteral i) = show i
    show (RealLiteral r) = show r

instance TranslateTyped PrimitiveLiteral where
    ttype (IntLiteral _) = IntT
    ttype (RealLiteral _) = RealT

data Atom
    = Var Var
    | Lit PrimitiveLiteral

instance Show Atom where
    show (Var v) = show v
    show (Lit lit) = show lit

data CodegenExpr
    = Let [Binding] CodegenExpr
    | Case CodegenExpr (NE.NonEmpty Alternative)
    | Application Var [Atom]
    | PrimApp B.PrimitiveFunction [Atom]
    | ConsApp P.Identifier [Atom]
    -- | Literal PrimitiveLiteral
    | PackedTuple [Atom]
    | Projector Int Var
    | Free Var CodegenExpr
    | Error

instance Show CodegenExpr where
    show = intercalate "\n" . prettyPrintCodegenExpr
    -- show (Let bindings body) = "let {" ++ intercalate " and " (map show bindings) ++ "} in " ++ show body
    -- show (Case disc branches) = "case " ++ show disc ++ " of " ++ foldMap (('\n' :) . show) branches
    -- show (Application fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    -- show (PrimApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    -- show (ConsApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    -- -- show (Literal lit) = show lit
    -- show (PackedTuple vs) = "(" ++ intercalate ", " (map show vs) ++ ")"
    -- show (Projector i v) = "sel-" ++ show i ++ " " ++ show v
    -- show (Free v expr) = "free " ++ show v ++ "; (" ++ show expr ++ ")"
    -- show Error = "error"

prettyPrintCodegenExpr :: CodegenExpr -> [String]
prettyPrintCodegenExpr (Let [] body) = "let {} in" : map (indent 4) (prettyPrintCodegenExpr body)
prettyPrintCodegenExpr (Let bindings body) =
    let showBinds = map prettyPrintBinding bindings
        bindLines = concat (mapHT (mapHT ("let { " ++) (indent 6)) (mapHT ("    ; " ++) (indent 6)) showBinds)
        rest = "    } in" : map (indent 4) (prettyPrintCodegenExpr body)
     in bindLines ++ rest
prettyPrintCodegenExpr (Case disc branches) =
    let showDisc = mapLast (++ " of") (mapHT ("case " ++) (indent 5) (prettyPrintCodegenExpr disc))
        showBranches = map prettyPrintAlt (NE.toList branches)
        branchLines = concat (mapHT (mapHT ("    { " ++) (indent 6)) (mapHT ("    ; " ++) (indent 6)) showBranches)
     in showDisc ++ branchLines ++ ["    }"]
prettyPrintCodegenExpr (Application fun args) = [show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"]
prettyPrintCodegenExpr (PrimApp fun args) = [show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"]
prettyPrintCodegenExpr (ConsApp fun args) = [show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"]
prettyPrintCodegenExpr (PackedTuple vs) = ["(" ++ intercalate ", " (map show vs) ++ ")"]
prettyPrintCodegenExpr (Projector i v) = ["sel-" ++ show i ++ " " ++ show v]
prettyPrintCodegenExpr (Free v expr) = ("free " ++ show v ++ ";") : prettyPrintCodegenExpr expr
prettyPrintCodegenExpr Error = ["error"]

indent :: Int -> String -> String
indent n = (replicate n ' ' ++)

mapHT :: (a -> a) -> (a -> a) -> [a] -> [a]
mapHT _ _ [] = []
mapHT fh ft (x:xs) = fh x : map ft xs

mapLast :: (a -> a) -> [a] -> [a]
mapLast f [x] = [f x]
mapLast f (x:xs) = x : mapLast f xs

data Binding
    = LazyBinding (Maybe P.Identifier) TypedVar LambdaForm
--    | EagerBinding (Maybe P.Identifier) TypedVar CodegenExpr

instance Show Binding where
    show (LazyBinding (Just (P.I n)) v lf) = show v ++ "(" ++ n ++ ") = " ++ show lf
    show (LazyBinding Nothing v lf) = show v ++ " = " ++ show lf
--     show (EagerBinding (Just (P.I n)) v expr) = show v ++ "[" ++ n ++ "] = " ++ show expr
--     show (EagerBinding Nothing p expr) = show p ++ " = " ++ show expr

prettyPrintBinding :: Binding -> [String]
prettyPrintBinding (LazyBinding (Just (P.I n)) v lf) = mapHT ((show v ++ "(" ++ n ++ ") = ") ++) id (prettyPrintLF lf)
prettyPrintBinding (LazyBinding Nothing v lf) = mapHT ((show v ++ " = ") ++) id (prettyPrintLF lf)

data Pattern
    = VarPattern TypedVar
    | LitPattern PrimitiveLiteral
    -- = AtomPattern AtomPattern
    | ConsPattern P.Identifier [Pattern]
    | TuplePattern [Pattern]
    -- | Ignore

instance Show Pattern where
    show (VarPattern v) = show v
    show (LitPattern lit) = show lit
    -- show (AtomPattern p) = show p
    show (ConsPattern name ps) = "(" ++ show name ++ concatMap ((' ':) . show) ps ++ ")"
    show (TuplePattern ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
    -- show Ignore = "_"

headNormalPattern :: Pattern -> Pattern
headNormalPattern (VarPattern v) = VarPattern (v { varType = headNormal (varType v) })
headNormalPattern lit@(LitPattern _) = lit
headNormalPattern (ConsPattern name ps) = ConsPattern name (map headNormalPattern ps)
headNormalPattern (TuplePattern ts) = TuplePattern (map headNormalPattern ts)

-- instance TranslateTyped Pattern where
--     ttype (VarPattern tv) = varType tv
--     ttype (LitPattern lit) = ttype lit
--     ttype (ConsPattern {}) = undefined
--     ttype (TuplePattern ts) = Tuple (map ttype ts)

data LambdaForm = Lf [Var] [TypedVar] CodegenExpr

instance Show LambdaForm where
    show (Lf captures args body) = "{" ++ intercalate ", " (map show captures) ++ "} \\{" 
        ++ intercalate ", " (map show args) ++ "} -> " ++ show body

prettyPrintLF :: LambdaForm -> [String]
prettyPrintLF (Lf captures args expr) =
    ("{" ++ intercalate ", " (map show captures) ++ "} \\{" ++ intercalate ", " (map show args) ++ "} ->")
    : map (indent 4) (prettyPrintCodegenExpr expr)

data Alternative = Alt Pattern CodegenExpr

instance Show Alternative where
    show (Alt pattern body) = "| " ++ show pattern ++ " -> " ++ show body

prettyPrintAlt :: Alternative -> [String]
prettyPrintAlt (Alt pat expr) = (show pat ++ " ->") : map (indent 4) (prettyPrintCodegenExpr expr)

-- failAlt :: Alternative
-- failAlt = Alt Ignore Error

type IdMap = M.HashMap P.Identifier (Var, Var)

data TranslatorContext = TranslatorContext
    { _idMap :: IdMap
    , _bound :: S.HashSet Var
    , _guaranteed :: Bool
    }

makeLenses ''TranslatorContext

data TranslatorState = TranslatorState
    { _nextVar :: Integer
    , _strictness :: M.HashMap Var [Bool]
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
        -- extractName (EagerBinding _ v _) = S.singleton (baseVar v)
        findBindFVs (LazyBinding _ _ (Lf _ binds e)) =
            local (bound %~ S.union (S.fromList (map baseVar binds))) $ findFVs e
        -- findBindFVs (EagerBinding _ _ e) = findFVs e
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
-- findFVs (Literal lit) = pure S.empty
findFVs (PackedTuple ts) = S.unions <$> mapM checkAtom ts
findFVs (Projector _ v) = checkFV v
findFVs (Free _ expr) = findFVs expr
findFVs Error = pure S.empty

checkAtom :: Atom -> Translator (S.HashSet Var)
checkAtom (Var v) = checkFV v
checkAtom _ = pure S.empty

checkFV :: Var -> Translator (S.HashSet Var)
checkFV v = do
    isBound <- asks (S.member v . (^. bound))
    if isBound
       then pure S.empty
       else pure (S.singleton v)

namesInPattern :: Pattern -> S.HashSet Var
namesInPattern (VarPattern v) = S.singleton (baseVar v)
namesInPattern (LitPattern _) = S.empty
namesInPattern (ConsPattern _ ps) = S.unions (map namesInPattern ps)
namesInPattern (TuplePattern ts) = S.unions (map namesInPattern ts)

convertAST :: T.StaticContext -> T.MultiplicityPoset -> T.TypedExpr -> CodegenExpr
convertAST staticContext poset expr =
    let initCtx = TranslatorContext
            { _idMap = M.empty
            , _bound = S.empty
            , _guaranteed = True
            }
        initState = TranslatorState
            { _nextVar = 0
            , _strictness = M.empty
            }
     in evalState (runReaderT (convert expr) initCtx) initState
    where
        -- finalise :: CodegenExpr -> CodegenExpr
        -- finalise (Let binds expr) = Let (map finaliseBind binds) (finalise expr)
        --     where
        --         finaliseBind :: Binding -> Binding
        --         finaliseBind (LazyBinding name v (Lf caps args body)) =
        --             LazyBinding name v (Lf caps args (finalise body))
        -- finalise (Case disc bs) = Case (finalise disc) (NE.map finaliseAlt bs)
        --     where
        --         finaliseAlt :: Alternative -> Alternative
        --         finaliseAlt (Alt pat body) = Alt pat (finalise body)
        -- finalise expr = expr

        convert :: T.TypedExpr -> Translator CodegenExpr
        convert (T.Let _ bindings body) = do
            gu <- asks (^. guaranteed)
            (makeBinds, ids) <- createBindings gu bindings
            local (idMap %~ M.union ids) $ do
                (binds, projection) <- makeBinds
                graph <- buildOrderGraph binds
                cvtBody <- convert body
                pure (buildLetPath (projection cvtBody) (stronglyConnComp graph))
            where
                createBindings :: Bool -> [T.TypedLetBinding]
                               -> Translator (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                createBindings _ [] = pure (pure ([], id), M.empty)
                createBindings gu ((T.TypedLetBinding mul pat@(T.VariablePattern t name) expr):binds)
                    -- Strict functions generate only strict
                    | isFunctionType t && ((isRelevant mul && gu) || nonDataHolder t) = do
                        (strictFunc, strictBindVar) <- makeThunk (Just pat) expr True
                        (restBinds, ids) <- createBindings gu binds
                        pure (addBinding strictFunc restBinds, M.insert name (strictBindVar, strictBindVar) ids)
                    -- Functions which are non strict should generate
                    -- both strict and non strict thunks (with no projectors)
                    | isFunctionType t && not (isRelevant mul && gu) = do
                        (strictFunc, strictBindVar) <- makeThunk (Just pat) expr True
                        (nonStrictFunc, nonStrictBindVar) <- makeThunk (Just pat) expr False
                        (restBinds, ids) <- createBindings gu binds
                        let binds' = addBinding nonStrictFunc restBinds
                            binds'' = addBinding strictFunc binds'
                            ids' = M.insert name (strictBindVar, nonStrictBindVar) ids
                        pure (binds'', ids')
                createBindings gu ((T.TypedLetBinding mul pattern expr):binds)
                    -- All other strict patterns should add a case expression to the binding body
                    | isRelevant mul && gu = do
                        (p, patIds) <- convertPattern pattern
                        let patIds' = M.map (\v -> (baseVar v, baseVar v)) patIds
                            addedNameSet = M.keysSet patIds
                            caseExpr = do
                                cvtExpr <- local (idMap %~ M.filterWithKey (\k _ -> not (k `S.member` addedNameSet))) $ convert expr
                                pure (Case cvtExpr . NE.singleton . Alt (headNormalPattern p))
                        (restBinds, ids) <- createBindings gu binds
                        pure (addPatternMatch caseExpr restBinds, M.union patIds' ids)
                    -- Lazy patterns which can be directly projected from generate
                    -- non strict thunks and projectors
                    | directProjection pattern = do
                        (nonStrictFunc, nonStrictBindVar) <- makeThunk (Just pattern) expr False
                        (restBinds, ids) <- createBindings gu binds
                        case pattern of
                          T.VariablePattern t name -> do
                              pure (addBinding nonStrictFunc restBinds,
                                    M.insert name (nonStrictBindVar, nonStrictBindVar) ids)
                          T.LiteralPattern (P.TupleLiteral ts) -> do
                              projVars <- forM ts $ \(T.VariablePattern t name) -> do
                                  projVar <- freshName
                                  pure (name, TV projVar (ttype t))
                              foldM (addProjector nonStrictBindVar)
                                  (addBinding nonStrictFunc restBinds, ids) (zip projVars [0..])
                    -- Non-trivial patterns generate non strict thunks which
                    -- extract values and non strict projectors
                    | otherwise = do
                        bindVar <- freshName
                        (p, patIds) <- convertPattern pattern
                        (restBinds, ids) <- createBindings gu binds
                        let patList = M.toList patIds
                            extractExpr = do
                                (Lf caps args cvtExpr) <- local ( (guaranteed .~ False)
                                                                . (bound %~ S.insert bindVar)
                                                                ) $ convertLambdas expr
                                let tupleType = Boxed (Tuple (map (varType . snd) patList))
                                    match = Alt p (PackedTuple (map (Var . baseVar . snd) patList))
                                    extractor = Case cvtExpr (NE.singleton match)
                                pure (LazyBinding Nothing (TV bindVar tupleType) (Lf caps args extractor))
                            binds' = addBinding extractExpr restBinds
                        foldM (addProjector bindVar) (binds', ids) (zip patList [0..])
                    where
                        addProjector :: Var
                                     -> (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                                     -> ((P.Identifier, TypedVar), Int)
                                     -> Translator (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                        addProjector var (binds, ids) ((name, projVar), index) = do
                            let lf = Lf [var] [] (Projector index var)
                                binding = LazyBinding (Just name) projVar lf
                                binds' = addBinding (pure binding) binds
                                ids' = M.insert name (baseVar projVar, baseVar projVar) ids
                            pure (binds', ids')

                isFunctionType :: T.Type -> Bool
                isFunctionType (T.FunctionType {}) = True
                isFunctionType _ = False

                nonDataHolder :: T.Type -> Bool
                nonDataHolder (T.FunctionType _ _ to) = nonDataHolder to
                nonDataHolder (T.Ground (P.I "Int")) = True
                nonDataHolder _ = False

                addBinding :: Translator Binding
                           -> Translator ([Binding], CodegenExpr -> CodegenExpr)
                           -> Translator ([Binding], CodegenExpr -> CodegenExpr)
                addBinding getBind getBinds = do
                    bind <- getBind
                    (binds, fn) <- getBinds
                    pure (bind:binds, fn)

                addPatternMatch :: Translator (CodegenExpr -> CodegenExpr)
                                -> Translator ([Binding], CodegenExpr -> CodegenExpr)
                                -> Translator ([Binding], CodegenExpr -> CodegenExpr)
                addPatternMatch getFn getBinds = do
                    fn <- getFn
                    (binds, fn') <- getBinds
                    pure (binds, fn . fn')

                directProjection :: T.Pattern -> Bool
                directProjection (T.VariablePattern {}) = True
                directProjection (T.LiteralPattern (P.TupleLiteral ts)) = all isVarPattern ts
                directProjection _ = False

                isVarPattern :: T.Pattern -> Bool
                isVarPattern (T.VariablePattern {}) = True
                isVarPattern _ = False

                buildOrderGraph :: [Binding] -> Translator [(Binding, Integer, [Integer])]
                buildOrderGraph [] = pure []
                buildOrderGraph (bind@(LazyBinding _ v (Lf caps _ _)):bs) = do
                    let node = (bind, (varID . baseVar) v, map varID caps)
                    (node:) <$> buildOrderGraph bs

                buildLetPath :: CodegenExpr -> [SCC Binding] -> CodegenExpr
                buildLetPath base [] = base
                buildLetPath base (AcyclicSCC v:sccs) = Let [v] (buildLetPath base sccs)
                buildLetPath base (CyclicSCC vs:sccs) = Let vs (buildLetPath base sccs)

        convert (T.Case _ mul disc branches) = do
            -- The discriminator is only GU if the expression is GU and the discriminator
            -- is relevant
            cvtDisc <- local (guaranteed %~ (&& isRelevant mul)) (convert disc)
            gu <- asks (^. guaranteed)
            -- Branches are GU if the expression is GU
            cvtBranches <- mapM (cvtBranch (gu && isRelevant mul)) branches
            pure (Case cvtDisc cvtBranches)
            where
                cvtBranch :: Bool -> T.TypedCaseBranch -> Translator Alternative
                cvtBranch strict (T.TypedCaseBranch pat branch) = do
                    (p, ids) <- convertPattern pat
                    let ids' = M.map (\v -> (baseVar v, baseVar v)) ids
                    cvtBranch <- local (idMap %~ M.union ids') $ convert branch
                    pure (Alt p cvtBranch)

        convert (T.Application _ fun arg) = do
            let (T.FunctionType _ (T.Arrow mul) _) = typeof fun
            collectArgs fun [(mul, arg)]
            where
                collectArgs :: T.TypedExpr -> [(Multiplicity, T.TypedExpr)] -> Translator CodegenExpr
                collectArgs (T.Application _ f a) args =
                    let (T.FunctionType _ (T.Arrow mul) _) = typeof f
                     in collectArgs f ((mul, a):args)
                collectArgs var@(T.Variable t name@(P.I rawName)) args
                    | isJust (B.getPrimitive name) = do
                        gu <- asks (^. guaranteed)
                        liftArgs (map (\(m, e) -> (gu && isRelevant m, e)) args) (PrimApp (fromJust (B.getPrimitive name)))
                    | rawName == "MkInt#" = do
                        gu <- asks (^. guaranteed)
                        liftArgs (map (\(m, e) -> (gu && isRelevant m, e)) args) (ConsApp name)
                    | rawName == "MkReal#" = do
                        gu <- asks (^. guaranteed)
                        liftArgs (map (\(m, e) -> (gu && isRelevant m, e)) args) (ConsApp name)
                    | M.member name (staticContext ^. T.dataConstructors) =
                        liftArgs (map (\(_, expr) -> (False, expr)) args) (ConsApp name)
                    | otherwise = do
                        funVar <- lookupVar name
                        gu <- asks (^. guaranteed)
                        case funVar of
                          Just v -> do
                              argStrictness <- gets ((M.! v) . (^. strictness))
                              liftArgs (zipWith (\s (_, e) -> (s, e)) argStrictness args) (Application v)
                          Nothing -> pure Error
                collectArgs expr args = do
                    -- Innermost function is GU if the application is GU
                    funExpr <- convert expr
                    gu <- asks (^. guaranteed)
                    case funExpr of
                      Let binds (Application funVar []) -> do
                          liftArgs (map (\(m, e) -> (gu && isRelevant m, e)) args) (Let binds . Application funVar)
                      _ -> do
                          let funTy = ttype (typeof expr)
                          funVar <- freshName
                          let alt = Alt (VarPattern (TV funVar funTy)) . Application funVar
                              caseExpr = Case funExpr . NE.singleton . alt
                          liftArgs (map (\(m, e) -> (gu && isRelevant m, e)) args) caseExpr

                liftArgs :: [(Bool, T.TypedExpr)] -> ([Atom] -> CodegenExpr) -> Translator CodegenExpr
                liftArgs args app = do
                    (argVars, binds, projectors) <- unzip3 <$> mapM (uncurry liftFuncArg) args
                    let combinedProjector = foldr (.) id projectors
                    pure (Let (catMaybes binds) (combinedProjector (app argVars)))

        convert lam@(T.Lambda t _ _ _) = do
            gu <- asks (^. guaranteed)
            (mkBind, var) <- makeThunk Nothing lam gu
            bind <- mkBind
            pure (Let [bind] (Application var []))
            -- let lambdaTy = ttype t
            -- lambdaName <- freshName
            -- bind <- LazyBinding Nothing (TV lambdaName lambdaTy) <$> convertLambdas lam
            -- pure (Let [bind] (Application lambdaName []))

        convert (T.Variable t name)
            | isJust (B.getPrimitive name) = pure (PrimApp (fromJust (B.getPrimitive name)) [])
            | M.member name (staticContext ^. T.dataConstructors) = pure (ConsApp name [])
            | otherwise = do
                funVar <- lookupVar name
                case funVar of
                  Just v -> pure (Application v [])
                  Nothing -> pure Error

        convert (T.Literal t lit) = convertLit lit
            where
                convertLit :: P.Literal T.TypedExpr -> Translator CodegenExpr
                convertLit (P.IntLiteral i) = pure (ConsApp (P.I "MkInt#") [Lit (IntLiteral i)])
                    -- gu <- asks (^. guaranteed)
                    -- if gu
                    --    then pure (Literal (IntLiteral i))
                    --    else pure (ConsApp (P.I "MkInt") [Lit (IntLiteral i)])
                convertLit (P.RealLiteral r) = pure (ConsApp (P.I "MkReal#") [Lit (RealLiteral r)])
                    -- gu <- asks (^. guaranteed)
                    -- if gu
                    --    then pure (Literal (RealLiteral r))
                    --    else pure (ConsApp (P.I "MkReal") [Lit (RealLiteral r)])
                convertLit (P.ListLiteral ls) =
                    makeList ls
                    where
                        makeList :: [T.TypedExpr] -> Translator CodegenExpr
                        makeList [] = pure (ConsApp (P.I "[]") [])
                        makeList (e:es) = do
                            eName <- freshName
                            cvtE <- convertLambdas e
                            esName <- freshName
                            cvtEs <- makeList es
                            esFvs <- S.toList <$> findFVs cvtEs
                            let bindE = LazyBinding Nothing (TV eName (ttype (typeof e))) cvtE
                                bindEs = LazyBinding Nothing (TV esName (ttype t)) (Lf esFvs [] cvtEs)
                                consCell = ConsApp (P.I "::") [Var eName, Var esName]
                            pure (Let [bindE, bindEs] consCell)
                convertLit (P.TupleLiteral ts) = do
                    gu <- asks (^. guaranteed)
                    (argVars, binds, projectors) <- unzip3 <$> mapM (liftFuncArg gu) ts
                    let combinedProjector = foldr (.) id projectors
                    pure (Let (catMaybes binds) (combinedProjector (PackedTuple argVars)))

        nameForPattern :: T.Pattern -> Maybe P.Identifier
        nameForPattern (T.VariablePattern _ name) = Just name
        nameForPattern _ = Nothing

        convertPattern :: T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
        convertPattern (T.VariablePattern t name) = do
            v <- freshName
            pure (VarPattern (TV v (ttype t)), M.singleton name (TV v (ttype t)))
        convertPattern (T.ConstructorPattern name ps) = do
            (ps', maps) <- mapAndUnzipM convertPattern ps
            pure (ConsPattern name ps', M.unions maps)
        convertPattern (T.LiteralPattern lit) = convertLitPattern lit
            where
                convertLitPattern :: P.Literal T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
                convertLitPattern (P.IntLiteral i) = pure (ConsPattern (P.I "MkInt#") [LitPattern (IntLiteral i)], M.empty)
                convertLitPattern (P.RealLiteral r) = pure (ConsPattern (P.I "MkReal#") [LitPattern (RealLiteral r)], M.empty)
                convertLitPattern (P.ListLiteral ps) = do
                    (ps', maps) <- mapAndUnzipM convertPattern ps
                    pure (foldr (\x xs -> ConsPattern (P.I "::") [x, xs]) (ConsPattern (P.I "[]") []) ps', M.unions maps)
                convertLitPattern (P.TupleLiteral ps) = do
                    (ps', maps) <- mapAndUnzipM convertPattern ps
                    pure (TuplePattern ps', M.unions maps)

        makeThunk :: Maybe T.Pattern -> T.TypedExpr -> Bool -> Translator (Translator Binding, Var)
        makeThunk pattern expr gu = do
            bindVar <- freshName
            modify (strictness %~ M.insert bindVar (getArgStrictness gu (typeof expr)))
            let name' = ((if gu then P.I "_@strict_" else mempty) <>) <$> (nameForPattern =<< pattern)
                bodyType = if gu then headNormal (lambdaBodyType expr) else lambdaBodyType expr
                binding = do
                    lf@(Lf _ args _) <- local ( (guaranteed .~ gu)
                                                 . (bound %~ id) -- S.insert bindVar)
                                                 ) $ convertLambdas expr
                    let thunkType =
                            case args of
                              [] -> bodyType
                              _ -> Function (weakNormal bodyType) (map varType args)
                    pure (LazyBinding name' (TV bindVar thunkType) lf)
            pure (binding, bindVar)
            where
                lambdaBodyType :: T.TypedExpr -> TranslateType
                lambdaBodyType (T.Lambda _ _ _ body) = lambdaBodyType body
                lambdaBodyType e = ttype (typeof e)

        convertLambdas :: T.TypedExpr -> Translator LambdaForm
        convertLambdas lam@(T.Lambda (T.FunctionType from _ _) mul _ _) = do
            gu <- asks (^. guaranteed)
            varName <- freshName -- (getTypeFor mul from)
            modify (strictness %~ M.insert varName (getArgStrictness gu from))
            (vs, expr) <- case lam of
                            T.Lambda _ _ (T.VariablePattern _ name) body -> do
                                local (idMap %~ M.insert name (varName, varName)) $ collectLambdas' 1 [] body
                            T.Lambda _ mul pattern body -> collectLambdas' 1 [(varName, pattern, mul)] body
            fvs <- local (bound %~ S.union (S.fromList (varName:map baseVar vs))) $ findFVs expr
            let varType = if gu && isRelevant mul
                             then headNormal (ttype from)
                             else ttype from
            pure (Lf (S.toList fvs) (TV varName varType:vs) expr)
            where
                collectLambdas' :: Int -> [(Var, T.Pattern, Multiplicity)] -> T.TypedExpr
                                -> Translator ([TypedVar], CodegenExpr)
                collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
                    gu <- asks (^. guaranteed)
                    varName <- freshName -- (getTypeFor mul from)
                    modify (strictness %~ M.insert varName (getArgStrictness gu from))
                    (vs, expr) <- local (idMap %~ M.insert name (varName, varName)) $ collectLambdas' (depth + 1) toMatch body
                    let varType = if gu && isRelevant mul
                                     then headNormal (ttype from)
                                     else ttype from
                    pure (TV varName varType:vs, expr)
                collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul pattern body) = do
                    gu <- asks (^. guaranteed)
                    varName <- freshName -- (getTypeFor mul from)
                    (vs, expr) <- collectLambdas' (depth + 1) ((varName, pattern, mul):toMatch) body
                    let varType = if gu && isRelevant mul
                                     then headNormal (ttype from)
                                     else ttype from
                    pure (TV varName varType:vs, expr)
                collectLambdas' depth toMatch expr = do
                    base <- buildCases (reverse toMatch)
                    pure ([], base)
                    where
                        buildCases :: [(Var, T.Pattern, Multiplicity)] -> Translator CodegenExpr
                        buildCases [] = convert expr
                        buildCases ((v, pat, mul):rest) = do
                            gu <- asks (^. guaranteed)
                            (p, ids) <- convertPattern pat
                            local (idMap %~ M.union (M.map (\v -> (baseVar v, baseVar v)) ids)) $ do
                                -- baseExpr <- (if isAffine mul then Free v else id) <$> buildCases rest
                                baseExpr <- buildCases rest
                                let pattern
                                        | gu && isRelevant mul = p
                                        | otherwise = p
                                pure (Case (Application v []) (NE.singleton (Alt pattern baseExpr)))

        convertLambdas expr = do
            expr' <- convert expr
            fvs <- findFVs expr'
            pure (Lf (S.toList fvs) [] expr')

        lookupVar :: P.Identifier -> Translator (Maybe Var)
        lookupVar name = do
            gu <- asks (^. guaranteed)
            asks (((if gu then fst else snd) <$>) . M.lookup name . (^. idMap))

        liftFuncArg :: Bool -> T.TypedExpr
                    -> Translator (Atom, Maybe Binding, CodegenExpr -> CodegenExpr)
        liftFuncArg strict (T.Variable t name)
            | not (M.member name (staticContext ^. T.defaultFunctions))
            && not (M.member name (staticContext ^. T.dataConstructors)) = do
                gu <- asks (^. guaranteed)
                argVar <- fromJust <$> lookupVar name
                if strict
                   then do
                       matchVar <- freshName
                       let alt = Alt (VarPattern (TV matchVar (headNormal (ttype t))))
                           matcher = Case (Application argVar []) . NE.singleton . alt
                       pure (Var matchVar, Nothing, matcher)
                   else pure (Var argVar, Nothing, id)
        -- liftFuncArg (mul, arg@(T.Literal t lit))
        --     | primitive lit = do
        --         gu <- asks (^. guaranteed)
        --         if gu && isRelevant mul
        --            then pure (Lit (convertLit lit), Nothing, id)
        --            else do
        --                cvtArg <- local (guaranteed .~ False) $ convertLambdas arg
        --                bindVar <- freshName
        --                let binding = LazyBinding Nothing (TV bindVar (ttype t)) cvtArg
        --                pure (Var bindVar, Just binding, id)
        --     where
        --         primitive :: P.Literal a -> Bool
        --         primitive (P.IntLiteral _) = True
        --         primitive (P.RealLiteral _) = True
        --         primitive _ = False

        --         convertLit :: P.Literal T.TypedExpr -> PrimitiveLiteral
        --         convertLit (P.IntLiteral i) = IntLiteral i
        --         convertLit (P.RealLiteral r) = RealLiteral r
        liftFuncArg strict arg = do
            if strict
               then do
                   cvtArg <- convert arg
                   matchVar <- freshName
                   let alt = Alt (VarPattern (TV matchVar (headNormal (ttype (typeof arg)))))
                       matcher = Case cvtArg . NE.singleton . alt
                   pure (Var matchVar, Nothing, matcher)
               else do
                   cvtArg <- local (guaranteed .~ False) $ convertLambdas arg
                   bindVar <- freshName
                   let binding = LazyBinding Nothing (TV bindVar (ttype (typeof arg))) cvtArg
                   pure (Var bindVar, Just binding, id)

        isRelevant :: Multiplicity -> Bool
        isRelevant mul = P.leq mul (T.MAtom P.Relevant) poset

        isAffine :: Multiplicity -> Bool
        isAffine mul = P.leq mul (T.MAtom P.Affine) poset

        isLambda :: T.TypedExpr -> Bool
        isLambda (T.Lambda {}) = True
        isLambda _ = False

        getArgStrictness :: Bool -> T.Type -> [Bool]
        getArgStrictness gu (T.FunctionType _ (T.Arrow mul) to) = (gu && isRelevant mul) : getArgStrictness gu to
        getArgStrictness _ _ = []

        freshName :: Translator Var
        freshName = do
            v <- gets (^. nextVar)
            modify (nextVar %~ (+1))
            pure (V v)

testTranslate :: String -> CodegenExpr
testTranslate s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck Builtin.Builtin.defaultBuiltins parsed
     in convertAST Builtin.Builtin.defaultBuiltins poset typed

