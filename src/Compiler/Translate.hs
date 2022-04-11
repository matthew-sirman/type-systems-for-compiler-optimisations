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

-- import qualified IR.DataType as IR

import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import Data.Maybe (catMaybes, fromJust)
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

-- instance IR.DataTypeContainer T.Type where
--     datatype (T.Poly _) = voidPtr
--     datatype (T.Ground (P.I "Int")) = IR.FirstOrder IR.Int64T
--     datatype (T.Ground (P.I "Real")) = IR.FirstOrder IR.Real64T
--     datatype (T.FunctionType from _ to) =
--         case IR.datatype to of
--           IR.FunctionT res args -> IR.FunctionT res (IR.datatype from : args)
--           res -> IR.FunctionT res [IR.datatype from]
--     datatype (T.TupleType ts) = IR.Structure (map IR.datatype ts)
--     datatype _ = error "Not yet implemented!"
-- 
-- instance IR.DataTypeContainer a => IR.DataTypeContainer (P.Literal a) where
--     datatype (P.IntLiteral _) = IR.FirstOrder IR.Int64T
--     datatype (P.RealLiteral _) = IR.FirstOrder IR.Real64T
--     datatype (P.ListLiteral ls) = undefined
--     datatype (P.TupleLiteral ts) = IR.Pointer (IR.Structure (map IR.datatype ts))
-- 
-- instance IR.DataTypeContainer T.Pattern where
--     datatype (T.VariablePattern t _) = IR.datatype t
--     datatype (T.ConstructorPattern _ ts) = IR.Structure (map IR.datatype ts)
--     datatype (T.LiteralPattern lit) = IR.datatype lit

data Evaluation
    = Strict
    | Lazy
    deriving (Eq, Generic)

instance Hashable Evaluation

class TranslateTyped a where
    ttype :: a -> TranslateType

data TranslateType
    = IntT
    | RealT
    | Poly
    | Tuple [TranslateType]
    | Named P.Identifier
    | Function TranslateType [TranslateType]
    deriving Eq

instance Show TranslateType where
    show IntT = "int"
    show RealT = "real"
    show Poly = "<poly>"
    show (Tuple ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
    show (Named name) = show name
    show (Function res args) = show res ++ " (" ++ intercalate ", " (map show args) ++ ")"

instance TranslateTyped T.Type where
    ttype (T.Poly _) = Poly
    ttype (T.Ground (P.I "Int")) = IntT
    ttype (T.Ground (P.I "Real")) = RealT
    ttype (T.FunctionType from _ to) =
        case ttype to of
          Function res args -> Function res (ttype from : args)
          res -> Function res [ttype from]
    ttype (T.TupleType ts) = Tuple (map ttype ts)
    ttype _ = undefined

instance TranslateTyped a => TranslateTyped (P.Literal a) where
    ttype (P.IntLiteral _) = IntT
    ttype (P.RealLiteral _) = RealT
    ttype (P.ListLiteral _) = undefined
    ttype (P.TupleLiteral ts) = Tuple (map ttype ts)

instance TranslateTyped T.Pattern where
    ttype (T.VariablePattern t _) = ttype t
    ttype (T.ConstructorPattern _ ts) = undefined
    ttype (T.LiteralPattern lit) = ttype lit

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

-- instance IR.DataTypeContainer PrimitiveLiteral where
--     datatype (IntLiteral _) = IR.FirstOrder IR.Int64T
--     datatype (RealLiteral _) = IR.FirstOrder IR.Real64T

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
    | PackedTuple [Atom]
    | Projector Int Var
    | Free Var CodegenExpr
    | Error

instance Show CodegenExpr where
    show (Let bindings body) = "let {" ++ intercalate " and " (map show bindings) ++ "} in " ++ show body
    show (Case disc branches) = "case " ++ show disc ++ " of " ++ foldMap (('\n' :) . show) branches
    show (Application fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (PrimApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (ConsApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (Literal lit) = show lit
    show (PackedTuple vs) = "(" ++ intercalate ", " (map show vs) ++ ")"
    show (Projector i v) = "sel-" ++ show i ++ " " ++ show v
    show (Free v expr) = "free " ++ show v ++ "; (" ++ show expr ++ ")"
    show Error = "error"

data Binding
    = LazyBinding (Maybe P.Identifier) TypedVar LambdaForm
--    | EagerBinding (Maybe P.Identifier) TypedVar CodegenExpr

instance Show Binding where
    show (LazyBinding (Just (P.I n)) v lf) = show v ++ "[" ++ n ++ "] = " ++ show lf
    show (LazyBinding Nothing v lf) = show v ++ " = " ++ show lf
--     show (EagerBinding (Just (P.I n)) v expr) = show v ++ "[" ++ n ++ "] = " ++ show expr
--     show (EagerBinding Nothing p expr) = show p ++ " = " ++ show expr

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

-- instance TranslateTyped Pattern where
--     ttype (VarPattern tv) = varType tv
--     ttype (LitPattern lit) = ttype lit
--     ttype (ConsPattern {}) = undefined
--     ttype (TuplePattern ts) = Tuple (map ttype ts)

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
        ++ intercalate ", " (map showArg args) ++ "} -> " ++ show body
        where
            showArg :: (Bool, TypedVar) -> String
            showArg (True, var) = '!' : show var
            showArg (False, var) = show var

data Alternative = Alt Pattern CodegenExpr

instance Show Alternative where
    show (Alt pattern body) = "| " ++ show pattern ++ " -> " ++ show body

-- failAlt :: Alternative
-- failAlt = Alt Ignore Error

type IdMap = M.HashMap P.Identifier (Var, Var)

data TranslatorContext = TranslatorContext
    { _idMap :: IdMap
    , _bound :: S.HashSet Var
    , _guaranteed :: Bool
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
        -- extractName (EagerBinding _ v _) = S.singleton (baseVar v)
        findBindFVs (LazyBinding _ _ (Lf _ binds e)) =
            local (bound %~ S.union (S.fromList (map (baseVar . snd) binds))) $ findFVs e
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
findFVs (Literal lit) = pure S.empty
findFVs (PackedTuple ts) = S.unions <$> mapM checkAtom ts
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
namesInPattern (ConsPattern _ ps) = S.unions (map namesInPattern ps)
namesInPattern (TuplePattern ts) = S.unions (map namesInPattern ts)

convertAST :: T.TypedExpr -> T.MultiplicityPoset -> CodegenExpr
convertAST expr poset =
    let initCtx = TranslatorContext
            { _idMap = M.empty
            , _bound = S.empty
            , _guaranteed = True
            }
        initState = TranslatorState
            { _nextVar = 0
            }
     in finalise (evalState (runReaderT (convert expr) initCtx) initState)
    where
        finalise :: CodegenExpr -> CodegenExpr
        finalise (Let binds expr) = Let (map finaliseBind binds) (finalise expr)
            where
                finaliseBind :: Binding -> Binding
                finaliseBind (LazyBinding name v (Lf caps args body)) =
                    LazyBinding name v (Lf (filter (/= baseVar v) caps) args (finalise body))
        finalise (Case disc bs) = Case (finalise disc) (NE.map finaliseAlt bs)
            where
                finaliseAlt :: Alternative -> Alternative
                finaliseAlt (Alt pat body) = Alt pat (finalise body)
        finalise expr = expr

        convert :: T.TypedExpr -> Translator CodegenExpr
        convert (T.Let _ bindings body) = do
            gu <- asks (^. guaranteed)
            (makeBinds, ids) <- createBindings gu bindings
            local (idMap %~ M.union ids) $ do
                (binds, projection) <- makeBinds
                graph <- buildOrderGraph binds
                cvtBody <- convert body
                pure (buildLetPath (projection cvtBody) (stronglyConnComp graph))
            -- let allBoundNames = M.unions names
            -- local (idMap %~ M.union allBoundNames) $ do
            --     primary <- zipWithM (\bind nms ->
            --         local (bound %~ S.union (S.fromList (M.elems nms))) bind) primaryBindings names
            --     let allBindings = primary ++ concat projectors
            --     graph <- buildOrderGraph allBindings
            --     cvtBody <- convert body
            --     pure (buildLetPath cvtBody (stronglyConnComp graph))
            where
                createBindings :: Bool -> [T.TypedLetBinding]
                               -> Translator (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                createBindings _ [] = pure (pure ([], id), M.empty)
                createBindings gu ((T.TypedLetBinding mul pat@(T.VariablePattern t name) expr):binds)
                    -- Strict functions generate only strict
                    | isFunctionType t && ((isRelevant mul && gu) || nonDataHolder t) = do
                        (strictFunc, strictBindVar) <- makeFunc pat expr True
                        (restBinds, ids) <- createBindings gu binds
                        pure (addBinding strictFunc restBinds, M.insert name (strictBindVar, strictBindVar) ids)
                    -- Functions which are non strict should generate
                    -- both strict and non strict thunks (with no projectors)
                    | isFunctionType t && not (isRelevant mul && gu) = do
                        (strictFunc, strictBindVar) <- makeFunc pat expr True
                        (nonStrictFunc, nonStrictBindVar) <- makeFunc pat expr False
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
                                pure (Case cvtExpr . NE.singleton . Alt p)
                        (restBinds, ids) <- createBindings gu binds
                        pure (addPatternMatch caseExpr restBinds, M.union patIds' ids)
                    -- Lazy patterns which can be directly projected from generate
                    -- non strict thunks and projectors
                    | directProjection pattern = do
                        (nonStrictFunc, nonStrictBindVar) <- makeFunc pattern expr False
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
                                (Lf caps args cvtExpr) <- convertLambdas expr
                                let tupleType = Tuple (map (varType . snd) patList)
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

                    -- | directProjection pattern = do
                    --     (pat, patIds) <- convertPattern pattern
                    --     primaryBindVar <- freshName
                    --     let patVarList = M.toList patIds
                    --         primaryBinding
                    --             = LazyBinding (nameForPattern pattern) (TV primaryBindVar (ttype pattern)) <$> convertLambdas expr
                    --     makeProjectors primaryBinding patVarList
                    -- | otherwise = do
                    --     (pat, patIds) <- convertPattern pattern
                    --     primaryBindVar <- freshName
                    --     let patVarList = M.toList patIds
                    --         caseExpr = do
                    --             disc <- convertLambdas expr
                    --             pure
                    --         primaryBinding =
                    --             LazyBinding (nameForPattern pattern) (TV primaryBindVar _) <$> convertLambdas expr
                    --     undefined

                makeFunc :: T.Pattern -> T.TypedExpr -> Bool -> Translator (Translator Binding, Var)
                makeFunc pattern expr gu = do
                    bindVar <- freshName
                    let name' = ((if gu then P.I "_@strict_" else mempty) <>) <$> nameForPattern pattern
                        binding = do
                            lf <- local (guaranteed .~ gu) $ convertLambdas expr
                            pure (LazyBinding name' (TV bindVar (ttype pattern)) lf)
                    pure (binding, bindVar)

                isFunctionType :: T.Type -> Bool
                isFunctionType (T.FunctionType {}) = True
                isFunctionType _ = False

                nonDataHolder :: T.Type -> Bool
                nonDataHolder (T.FunctionType _ _ to) = nonDataHolder to
                nonDataHolder (T.Ground (P.I "Int")) = True
                nonDataHolder _ = False

                -- createBindings gu ((T.TypedLetBinding mul (T.VariablePattern t name) expr@(T.Lambda {})):binds) = do
                --     -- TODO: Add "sum-of-units type" check
                --     isGuaranteed <- asks (^. guaranteed)
                --     (strictFunc, strictVar) <- mkFunc True
                --     (restBinds, ids) <- createBindings binds
                --     let addedStrict = addBinding (Just strictFunc) (pure id) restBinds
                --     if relevant mul && isGuaranteed
                --        then pure (addedStrict, M.insert name (strictVar, strictVar) ids)
                --        else do
                --            (nonStrictFunc, nonStrictVar) <- mkFunc False
                --            undefiend
                --     where
                -- createBindings gu ((T.TypedLetBinding mul pat expr):binds) = do
                --     isGuaranteed <- asks (^. guaranteed)
                --     if isGuaranteed
                --        then undefined
                --        else undefined undefined
                --     undefined

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

                -- createEagerBind :: T.TypedLetBinding
                --                 -> Translator (Translator (CodegenExpr -> CodegenExpr), IdMap)
                -- createEagerBind (T.TypedLetBinding _ (T.VariablePattern t name) expr@(T.Lambda {})) = do
                --     bindVar <- freshName
                --     undefined
                -- createEagerBind (T.TypedLetBinding _ pattern expr) = do
                --     (p, ids) <- convertPattern pattern
                --     let caseExpr = do
                --             cvtExpr <- convert expr
                --             pure (Case cvtExpr . NE.singleton . Alt p)
                --     pure (caseExpr, ids)

                -- createLazyBind :: T.TypedLetBinding -> Translator (Translator Binding, [Binding], IdMap)
                -- createLazyBind (T.TypedLetBinding _ (T.VariablePattern t name) expr) = do
                --     bindVar <- freshName
                --     let bind = do
                --             lambdaForm <- convertLambdas expr
                --             pure (LazyBinding (Just name) (TV bindVar (ttype t)) lambdaForm)
                --     pure (bind, [], M.singleton name (bindVar, bindVar))

                -- createBind :: T.TypedLetBinding
                --            -> Translator (Maybe (Translator Binding, [Binding]), CodegenExpr -> CodegenExpr, IdMap)
                -- createBind (T.TypedLetBinding mul (T.VariablePattern t name) expr) = do
                --     bindVar <- freshName
                --     let bindTVar = TV bindVar (ttype eval t)
                --         bind = if isEager mul
                --                   then EagerBinding (Just name) bindTVar <$>
                --                            local (eager .~ True) (convert expr)
                --                   else LazyBinding (Just name) bindTVar <$>
                --                            local (eager .~ False) (convertLambdas expr)
                --     pure (bind, [], M.singleton name bindVar)
                -- createBind (T.TypedLetBinding mul pat@(T.LiteralPattern (P.TupleLiteral ts)) expr)
                --     | all isVarPattern ts = do
                --         bindVar <- freshName
                --         vars <- mapM (const freshName) ts
                --         let bindTVar = TV bindVar (ttype eval pat)
                --             bind = if isEager mul
                --                       then EagerBinding Nothing bindTVar <$>
                --                                local (eager .~ True) (convert expr)
                --                       else LazyBinding Nothing bindTVar <$>
                --                                local (eager .~ False) (convertLambdas expr)
                --         (ids, projectors) <- unzip <$> zipWithM (makeProjectorBinding bindVar) [0..] ts
                --         pure (bind, projectors, M.fromList ids)
                --     where
                --         makeProjectorBinding :: Var -> Int -> T.Pattern
                --                              -> Translator ((P.Identifier, Var), Binding)
                --         makeProjectorBinding capture index (T.VariablePattern t v)
                --             | isEager mul = do
                --                 bind <- freshName
                --                 let proj = Projector index capture
                --                     binding = EagerBinding (Just v) (TV bind (ttype eval t)) proj
                --                 pure ((v, bind), binding)
                --             | otherwise = do
                --                 bind <- freshName
                --                 let proj = Lf [capture] [] (Projector index capture)
                --                     binding = LazyBinding (Just v) (TV bind (ttype eval t)) proj
                --                 pure ((v, bind), binding)
                -- createBind (T.TypedLetBinding mul pat expr) = do
                --     bindVar <- freshName
                --     packedVar <- freshName
                --     let initState = BindingBuilderState
                --             { _varsBound = []
                --             }
                --     (unpack, bbs) <- runStateT (reformPattern bindVar pat) initState
                --     case bbs ^. varsBound of
                --       -- [] -> do
                --       --     let pvType = IR.Pointer (IR.Structure [])
                --       --         varExtractor = unpack (PackedTuple pvType [])

                --       --     pure (makeLetBinding (TV packedVar (wrapType pvType)) bindVar varExtractor, [], M.empty)
                --       [(v, name)] -> do
                --           let pvType = varType v
                --               varExtractor = unpack (Application (baseVar v) [])

                --           pure (makeLetBinding (Just name) (TV packedVar pvType) varExtractor, [], M.singleton name packedVar)
                --       vs -> do
                --           let pvType = Tuple (map (varType . fst) vs)
                --           nameMap <- mapM createNewVar vs
                --           let projBinds = zipWith (createProjBinding packedVar) nameMap [0..]
                --               varExtractor = unpack (PackedTuple pvType (map (Var . baseVar . fst) vs))

                --           pure (makeLetBinding Nothing (TV packedVar pvType) varExtractor, projBinds, M.fromList (map (baseVar <$>) nameMap))
                --     where
                --         createNewVar :: (TypedVar, P.Identifier) -> Translator (P.Identifier, TypedVar)
                --         createNewVar (v, name) = do
                --             v' <- freshName
                --             pure (name, TV v' (varType v))

                --         createProjBinding :: Var -> (P.Identifier, TypedVar) -> Int -> Binding
                --         createProjBinding capture (name, bindVar) index
                --             | isEager mul = EagerBinding (Just name) bindVar proj
                --             | otherwise = LazyBinding (Just name) bindVar (Lf [capture] [] proj)
                --             where
                --                 proj :: CodegenExpr
                --                 proj = Projector index capture

                --         makeLetBinding :: Maybe P.Identifier -> TypedVar -> (CodegenExpr -> CodegenExpr)
                --                        -> Translator Binding
                --         makeLetBinding name packedVar varExtractor
                --             | isEager mul = do
                --                 cvtExpr <- local (eager .~ True) $ convert expr
                --                 -- pure (EagerBinding (nameForPattern pat) bindVar (insertExpr varExtractor cvtExpr))
                --                 pure (EagerBinding name packedVar (varExtractor cvtExpr))
                --             | otherwise = do
                --                 (Lf caps args cvtExpr) <- local (eager .~ False) $ convertLambdas expr
                --                 let lambdaForm = Lf caps args (varExtractor cvtExpr)
                --                 pure (LazyBinding name packedVar lambdaForm)

                directProjection :: T.Pattern -> Bool
                directProjection (T.VariablePattern {}) = True
                directProjection (T.LiteralPattern (P.TupleLiteral ts)) = all isVarPattern ts
                directProjection _ = False

                isVarPattern :: T.Pattern -> Bool
                isVarPattern (T.VariablePattern {}) = True
                isVarPattern _ = False

                -- reformPattern :: Var -> T.Pattern -> BindingBuilder (CodegenExpr -> CodegenExpr -> CodegenExpr)
                -- reformPattern bv (T.VariablePattern t v) = do
                --     modify (varsBound %~ ((TV bv (ttype eval t), v):))
                --     pure const
                -- reformPattern bv (T.ConstructorPattern name ps) = undefined
                -- reformPattern bv (T.LiteralPattern lit) = reformPatternLit lit

                -- reformPatternLit :: P.Literal T.Pattern
                --                  -> BindingBuilder (CodegenExpr -> CodegenExpr -> CodegenExpr)
                -- reformPatternLit (P.IntLiteral i) = do
                --     let pattern = LitPattern (IntLiteral i)
                --         match rest disc = Case disc (NE.singleton (Alt pattern rest))
                --     pure match
                -- reformPatternLit (P.RealLiteral r) = do
                --     let pattern = LitPattern (RealLiteral r)
                --         match rest disc = Case disc (NE.singleton (Alt pattern rest))
                --     pure match
                -- reformPatternLit (P.ListLiteral ls) = undefined
                -- reformPatternLit (P.TupleLiteral ts) = do
                --     tempVars <- lift $ mapM (const freshName) ts
                --     subPatCombinators <- zipWithM reformPattern tempVars ts
                --     let subMatches = zipWith flip subPatCombinators [Application v [] | v <- tempVars]
                --         pattern = TuplePattern (map VarPattern tempVars)
                --         match rest disc = Case disc (NE.singleton (Alt pattern (foldr id rest subMatches)))
                --     pure match

                buildOrderGraph :: [Binding] -> Translator [(Binding, Integer, [Integer])]
                buildOrderGraph [] = pure []
                -- buildOrderGraph (bind@(EagerBinding _ v body):bs) = do
                --     fvs <- findFVs body
                --     let node = (bind, (varID . baseVar) v, map varID (S.toList fvs))
                --     (node:) <$> buildOrderGraph bs
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
            -- The discriminator is only GU if the expression is GU and the discriminator
            -- is relevant
            cvtDisc <- local (guaranteed %~ (&& isRelevant mul)) (convert disc)
            -- Branches are GU if the expression is GU
            cvtBranches <- mapM cvtBranch branches
            pure (Case cvtDisc cvtBranches)
            where
                cvtBranch :: T.TypedCaseBranch -> Translator Alternative
                cvtBranch (T.TypedCaseBranch pat branch) = do
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
                collectArgs var@(T.Variable _ name) args
                    | M.member name B.functions = liftArgs args (PrimApp name)
                    | M.member name Builtin.Builtin.constructors = liftArgs args (ConsApp name)
                    | otherwise = do
                        funVar <- lookupVar name
                        case funVar of
                          Just v -> liftArgs args (Application v)
                          Nothing -> pure Error
                collectArgs expr args = do
                    -- Innermost function is GU if the application is GU
                    funExpr <- convert expr
                    case funExpr of
                      Let binds (Application funVar []) -> do
                          liftArgs args (Let binds . Application funVar)
                      _ -> do
                          let funTy = ttype (typeof expr)
                          funVar <- freshName
                          let alt = Alt (VarPattern funVar) . Application funVar
                              caseExpr = Case funExpr . NE.singleton . alt
                          liftArgs args caseExpr

                liftArgs :: [(Multiplicity, T.TypedExpr)] -> ([Atom] -> CodegenExpr) -> Translator CodegenExpr
                liftArgs args app = do
                    (argVars, binds, projectors) <- unzip3 <$> mapM liftFuncArg args
                    let combinedProjector = foldr (.) id projectors
                    pure (Let (catMaybes binds) (combinedProjector (app argVars)))

        convert lam@(T.Lambda t _ _ _) = do
            let lambdaTy = ttype t
            lambdaName <- freshName
            bind <- LazyBinding Nothing (TV lambdaName lambdaTy) <$> convertLambdas lam
            pure (Let [bind] (Application lambdaName []))

        convert (T.Variable _ name) = do
            v <- lookupVar name
            case v of
              Just vName -> pure (Application vName [])
              Nothing -> pure Error

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
                    gu <- asks (^. guaranteed)
                    (argVars, binds, projectors) <- unzip3 <$> mapM (liftFuncArg . (MAtom P.Linear,)) ts
                    let combinedProjector = foldr (.) id projectors
                    pure (Let (catMaybes binds) (combinedProjector (PackedTuple argVars)))

        convertPattern :: T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
        convertPattern (T.VariablePattern t name) = do
            v <- freshName
            pure (VarPattern v, M.singleton name (TV v (ttype t)))
        convertPattern (T.ConstructorPattern name ps) = undefined
        convertPattern (T.LiteralPattern lit) = convertLitPattern lit
            where
                convertLitPattern :: P.Literal T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
                convertLitPattern (P.IntLiteral i) = pure (LitPattern (IntLiteral i), M.empty)
                convertLitPattern (P.RealLiteral r) = pure (LitPattern (RealLiteral r), M.empty)
                convertLitPattern (P.ListLiteral ls) = undefined
                convertLitPattern (P.TupleLiteral ts) = do
                    (ps, maps) <- unzip <$> mapM convertPattern ts
                    pure (TuplePattern ps, M.unions maps)

        convertLambdas :: T.TypedExpr -> Translator LambdaForm
        convertLambdas lam@(T.Lambda (T.FunctionType from _ _) mul _ _) = do
            varName <- freshName -- (getTypeFor mul from)
            gu <- asks (^. guaranteed)
            (vs, expr) <- case lam of
                            T.Lambda _ _ (T.VariablePattern _ name) body -> do
                                local (idMap %~ M.insert name (varName, varName)) $ collectLambdas' 1 [] body
                            T.Lambda _ mul pattern body -> collectLambdas' 1 [(varName, pattern, mul)] body
            fvs <- local (bound %~ S.union (S.fromList (varName:map (baseVar . snd) vs))) $ findFVs expr
            pure (Lf (S.toList fvs) ((gu && isRelevant mul, TV varName (ttype from)):vs) expr)
            where
                collectLambdas' :: Int -> [(Var, T.Pattern, Multiplicity)] -> T.TypedExpr
                                -> Translator ([(Bool, TypedVar)], CodegenExpr)
                collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
                    gu <- asks (^. guaranteed)
                    varName <- freshName -- (getTypeFor mul from)
                    (vs, expr) <- local (idMap %~ M.insert name (varName, varName)) $ collectLambdas' (depth + 1) toMatch body
                    pure ((gu && isRelevant mul, TV varName (ttype from)):vs, expr)
                collectLambdas' depth toMatch (T.Lambda (T.FunctionType from _ _) mul pattern body) = do
                    gu <- asks (^. guaranteed)
                    varName <- freshName -- (getTypeFor mul from)
                    (vs, expr) <- collectLambdas' (depth + 1) ((varName, pattern, mul):toMatch) body
                    pure ((gu && isRelevant mul, TV varName (ttype from)):vs, expr)
                collectLambdas' depth toMatch expr = do
                    base <- buildCases (reverse toMatch)
                    pure ([], base)
                    where
                        buildCases :: [(Var, T.Pattern, Multiplicity)] -> Translator CodegenExpr
                        buildCases [] = convert expr
                        buildCases ((v, pat, mul):rest) = do
                            (p, ids) <- convertPattern pat
                            local (idMap %~ M.union (M.map (\v -> (baseVar v, baseVar v)) ids)) $ do
                                baseExpr <- (if isAffine mul then Free v else id) <$> buildCases rest
                                pure (Case (Application v []) (NE.singleton (Alt p baseExpr)))

        convertLambdas expr = do
            expr' <- convert expr
            fvs <- findFVs expr'
            pure (Lf (S.toList fvs) [] expr')

        lookupVar :: P.Identifier -> Translator (Maybe Var)
        lookupVar name = do
            gu <- asks (^. guaranteed)
            asks (((if gu then fst else snd) <$>) . M.lookup name . (^. idMap))

        liftFuncArg :: (Multiplicity, T.TypedExpr)
                -> Translator (Atom, Maybe Binding, CodegenExpr -> CodegenExpr)
        liftFuncArg (mul, T.Variable t name) = do
            gu <- asks (^. guaranteed)
            argVar <- fromJust <$> lookupVar name
            if gu && isRelevant mul
               then do
                   matchVar <- freshName
                   let alt = Alt (VarPattern matchVar)
                       matcher = Case (Application argVar []) . NE.singleton . alt
                   pure (Var matchVar, Nothing, matcher)
               else pure (Var argVar, Nothing, id)
        liftFuncArg (mul, arg) = do
            gu <- asks (^. guaranteed)
            if gu && isRelevant mul
               then do
                   cvtArg <- convert arg
                   matchVar <- freshName
                   let alt = Alt (VarPattern matchVar)
                       matcher = Case cvtArg . NE.singleton . alt
                   pure (Var matchVar, Nothing, matcher)
               else do
                   cvtArg <- local (guaranteed .~ False) $ convertLambdas arg
                   bindVar <- freshName
                   let binding = LazyBinding Nothing (TV bindVar (ttype (typeof arg))) cvtArg
                   pure (Var bindVar, Just binding, id)
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

        isRelevant :: Multiplicity -> Bool
        isRelevant mul = P.leq mul (T.MAtom P.Relevant) poset

        -- eval :: Multiplicity -> Evaluation
        -- eval mul = if isEager mul
        --               then Strict
        --               else Lazy

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
