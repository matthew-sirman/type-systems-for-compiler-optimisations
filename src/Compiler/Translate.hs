{-# LANGUAGE TemplateHaskell, DeriveGeneric, TupleSections, PatternSynonyms, RankNTypes #-}
module Compiler.Translate where

import qualified Util.ConstrainedPoset as P

import qualified Parser.AST as P
    ( Identifier(..)
    , Literal(..)
    , MultiplicityAtom(..)
    )

import qualified Typing.Types as T
import Typing.Types
    ( Multiplicity(..)
    , PrimitiveLiteral(..)
    , Arrow(..)
    , typeof
    )

import Builtin.Codegen as B

-- import qualified IR.DataType as IR

import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import Data.Maybe (catMaybes, fromJust, isJust, fromMaybe)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Graph
import Data.Fix

import Control.Applicative ((<|>))
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

newtype PolyVar = PolyVar Integer
    deriving (Eq, Generic)

instance Hashable PolyVar

instance Show PolyVar where
    show (PolyVar v) = "p" ++ show v

data TranslateType
    = IntT
    | RealT
    | Poly PolyVar
    | Tuple [TranslateType]
    | Named P.Identifier
    | TypeApp P.Identifier [TranslateType]
    | Function TranslateType [TranslateType]
    deriving Eq

instance Show TranslateType where
    show IntT = "int"
    show RealT = "real"
    show (Poly p) = show p
    show (Tuple ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
    show (Named name) = show name
    show (TypeApp base args) = show base ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (Function res args) = show res ++ " (" ++ intercalate ", " (map show args) ++ ")"

typeToTType :: T.Type -> TranslateType
typeToTType (T.Poly p) = Poly (PolyVar p)
typeToTType (T.Ground (P.I "Int#")) = IntT
typeToTType (T.Ground (P.I "Real#")) = RealT
typeToTType (T.Ground name) = Named name
typeToTType (T.FunctionType from (T.Arrow mul) to) =
    case typeToTType to of
      Function res args -> Function res (typeToTType from : args)
      res -> Function res [typeToTType from]
typeToTType (T.TupleType ts) = Tuple (map typeToTType ts)
typeToTType app@(T.TypeApp {}) = collectArgs app []
    where
        collectArgs :: T.Type -> [TranslateType] -> TranslateType
        collectArgs (T.TypeApp head arg) args =
            collectArgs head (typeToTType arg : args)
        collectArgs (T.Ground name) args = TypeApp name args
        collectArgs _ _ = error "Badly formed type"

ftvs :: TranslateType -> [PolyVar]
ftvs = S.toList . ftvs'
    where
        ftvs' :: TranslateType -> S.HashSet PolyVar
        ftvs' IntT = S.empty
        ftvs' RealT = S.empty
        ftvs' (Poly p) = S.singleton p
        ftvs' (Tuple ts) = S.unions (map ftvs' ts)
        ftvs' (Named _) = S.empty
        ftvs' (TypeApp _ ts) = S.unions (map ftvs' ts)
        ftvs' (Function ret args) = S.unions (ftvs' ret : map ftvs' args)

newtype Var = V
    { varID :: Integer
    }
    deriving (Eq, Generic)

instance Show Var where
    show (V x) = "$" ++ show x

instance Hashable Var

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

data Atom
    = Var Var
    | Lit PrimitiveLiteral

instance Show Atom where
    show (Var v) = show v
    show (Lit lit) = show lit

type Tag = Integer

data TaggedTExprF t = Tagged
    { expr_ :: T.TypedExprF t
    , tag_ :: Tag
    }

type TaggedTExpr = Fix TaggedTExprF

expr :: TaggedTExpr -> T.TypedExprF TaggedTExpr
expr = expr_ . unFix

tag :: TaggedTExpr -> Tag
tag = tag_ . unFix

instance T.TypeContainer t => T.TypeContainer (TaggedTExprF t) where
    typeof = typeof . expr_

instance Functor TaggedTExprF where
    fmap f (Tagged expr tag) = Tagged (fmap f expr) tag

instance Foldable TaggedTExprF where
    foldr f e (Tagged expr _) = foldr f e expr

instance Traversable TaggedTExprF where
    traverse f (Tagged expr tag) = Tagged <$> traverse f expr <*> pure tag

pattern LetT t binds body <- Fix (Tagged (T.Let_ t binds body) _)
pattern CaseT t mul disc branches <- Fix (Tagged (T.Case_ t mul disc branches) _)
pattern ApplicationT t fun arg <- Fix (Tagged (T.Application_ t fun arg) _)
pattern LambdaT t mul pat body <- Fix (Tagged (T.Lambda_ t mul pat body) _)
pattern VariableT t name <- Fix (Tagged (T.Variable_ t name) _)
pattern TupleT t name <- Fix (Tagged (T.Tuple_ t name) _)
pattern LiteralT t lit <- Fix (Tagged (T.Literal_ t lit) _)

{-# COMPLETE LetT, CaseT, ApplicationT, LambdaT, VariableT, TupleT, LiteralT #-}

data CodegenExpr
    = Let [Binding] CodegenExpr
    | Case CodegenExpr (NE.NonEmpty Alternative)
    | Application (Bool, Bool) Var [Atom]
    | PrimApp Bool B.PrimitiveFunction [Atom]
    | ConsApp Bool P.Identifier [Atom]
    | PackedTuple [Atom]
    | Projector (Bool, Bool) Int Var
    | Error

instance Show CodegenExpr where
    show = intercalate "\n" . prettyPrintCodegenExpr

prettyPrintCodegenExpr :: CodegenExpr -> [String]
prettyPrintCodegenExpr (Let [] body) = "let {} in" : map (indent 4) (prettyPrintCodegenExpr body)
prettyPrintCodegenExpr (Let bindings body) =
    let showBinds = map prettyPrintBinding bindings
        bindLines = concat (mapHT (mapHT ("let { " ++) (indent 6)) (mapHT ("    ; " ++) (indent 6)) showBinds)
        rest = "    } in" : prettyPrintCodegenExpr body
     in bindLines ++ rest
prettyPrintCodegenExpr (Case disc branches) =
    let showDisc = mapLast (++ " of") (mapHT ("case " ++) (indent 5) (prettyPrintCodegenExpr disc))
        showBranches = map prettyPrintAlt (NE.toList branches)
        branchLines = concat (mapHT (mapHT ("    { " ++) (indent 6)) (mapHT ("    ; " ++) (indent 6)) showBranches)
     in showDisc ++ branchLines ++ ["    }"]
prettyPrintCodegenExpr (Application mul fun args) =
    [multiplicityString mul ++ show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"]
prettyPrintCodegenExpr (PrimApp _ fun args) = [show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"]
prettyPrintCodegenExpr (ConsApp free fun args) = [show fun ++ " {" ++ intercalate ", " (map show args) ++ "}" ++ if free then " (freeable)" else ""]
prettyPrintCodegenExpr (PackedTuple vs) = ["(" ++ intercalate ", " (map show vs) ++ ")"]
prettyPrintCodegenExpr (Projector mul i v) = ["sel-" ++ show i ++ " " ++ multiplicityString mul ++ show v]
prettyPrintCodegenExpr Error = ["error"]

multiplicityString :: (Bool, Bool) -> String
multiplicityString (True, True) = "!"
multiplicityString (True, False) = "+"
multiplicityString (False, True) = "?"
multiplicityString (False, False) = "*"

indent :: Int -> String -> String
indent n = (replicate n ' ' ++)

mapHT :: (a -> a) -> (a -> a) -> [a] -> [a]
mapHT _ _ [] = []
mapHT fh ft (x:xs) = fh x : map ft xs

mapLast :: (a -> a) -> [a] -> [a]
mapLast f [] = []
mapLast f [x] = [f x]
mapLast f (x:xs) = x : mapLast f xs

data Binding
    = LazyBinding String TypedVar LambdaForm
    | BoxBinding String Var Var
    | Reuse Var String Tag [(Bool, Var)]

prettyPrintBinding :: Binding -> [String]
prettyPrintBinding (LazyBinding name v lf) =
    let forallSpec = case ftvs (varType v) of
                       [] -> ""
                       ftvs -> "forall " ++ unwords (map show ftvs) ++ "."
     in (("[" ++ name ++ "]" ++ show v ++ " = ") ++ forallSpec) : map (indent 4) (prettyPrintLF lf)
prettyPrintBinding (BoxBinding name tv v) =
    ["[" ++ name ++ "]" ++ show tv ++ " = {} \\n {} -> [" ++ show v ++ "]"]
prettyPrintBinding (Reuse v name _ caps) =
    [show v ++ " = {" ++ intercalate ", " (map showCap caps) ++ "} -> reuse " ++ name]
    where
        showCap :: (Bool, Var) -> String
        showCap (True, v) = "[" ++ show v ++ "]"
        showCap (_, v) = show v

data Pattern
    = VarPattern TypedVar
    | LitPattern PrimitiveLiteral
    | ConsPattern P.Identifier [Pattern]
    | TuplePattern [Pattern]

instance Show Pattern where
    show (VarPattern v) = show v
    show (LitPattern lit) = show lit
    show (ConsPattern name ps) = "(" ++ show name ++ concatMap ((' ':) . show) ps ++ ")"
    show (TuplePattern ts) = "(" ++ intercalate ", " (map show ts) ++ ")"

data Alternative = Alt Bool Pattern CodegenExpr

prettyPrintAlt :: Alternative -> [String]
prettyPrintAlt (Alt free pat expr) =
    (show pat ++ " ->" ++ if free then " free pattern;" else "")
    : map (indent 4) (prettyPrintCodegenExpr expr)

data UpdateFlag = U | N
    deriving Eq

instance Show UpdateFlag where
    show U = "u"
    show N = "n"

data LambdaForm = Lf UpdateFlag [(Bool, Var)] [(Bool, TypedVar)] LambdaBody

data LambdaBody = LambdaBody
    { _linearBody :: Maybe CodegenExpr
    , _relevantBody :: Maybe CodegenExpr
    , _affineBody :: Maybe CodegenExpr
    , _normalBody :: Maybe CodegenExpr
    }

variants :: LambdaBody -> [CodegenExpr]
variants l = catMaybes [_linearBody l, _relevantBody l, _affineBody l, _normalBody l]

prettyPrintLF :: LambdaForm -> [String]
prettyPrintLF (Lf update captures args body) =
    let prefix = "{" ++ intercalate ", " (map showCap captures) ++ "} \\" ++ show update ++ " {" ++ intercalate ", " (map showArg args) ++ "} ->"
        lfs = intercalate [indent 4 "/\\"] (map (map (indent 4) . prettyPrintCodegenExpr) (variants body))
            -- case body of
            --     LazyOnly expr -> prefix : map (indent 4) (prettyPrintCodegenExpr expr)
            --     Both strict lazy -> prefix : map (indent 4) (prettyPrintCodegenExpr strict)
            --                      ++ (indent 4 "/\\" : map (indent 4) (prettyPrintCodegenExpr lazy))
     in prefix : lfs
    where
        showCap :: (Bool, Var) -> String
        showCap (True, v) = "[" ++ show v ++ "]"
        showCap (_, v) = show v

        showArg :: (Bool, TypedVar) -> String
        showArg (strict, v) = (if strict then "!" else "") ++ show v

makeLenses ''LambdaBody

firstBody :: LambdaBody -> Maybe CodegenExpr
firstBody l = l ^. linearBody <|> l ^. relevantBody <|> l ^. affineBody <|> l ^. normalBody

mapBodies :: (CodegenExpr -> CodegenExpr) -> LambdaBody -> LambdaBody
mapBodies f = (linearBody %~ fmap f) . (relevantBody %~ fmap f) . (affineBody %~ fmap f) . (normalBody %~ fmap f)

type IdMap = M.HashMap P.Identifier (Bool, Var)

data TranslatorContext = TranslatorContext
    { _idMap :: IdMap
    , _bound :: S.HashSet Var
    , _evalContext :: (Bool, Bool)
    }

makeLenses ''TranslatorContext

data TranslatorState = TranslatorState
    { _nextVar :: Integer
    , _strictness :: M.HashMap Var [Bool]
    , _builtBindings :: M.HashMap Tag LambdaForm
    , _builtPatterns :: M.HashMap Tag (Pattern, M.HashMap P.Identifier TypedVar)
    }

makeLenses ''TranslatorState

type Translator a = ReaderT TranslatorContext (State TranslatorState) a

findFVs :: S.HashSet Var -> CodegenExpr -> Translator (S.HashSet (Bool, Var))
findFVs svs (Let bindings body) = do
    bindFVs <- S.unions <$> mapM bindingFVs bindings
    bodyFVs <- local (bound %~ S.union allNames) $ findFVs svs body
    pure (S.union bodyFVs bindFVs)
    where
        bindingFVs :: Binding -> Translator (S.HashSet (Bool, Var))
        bindingFVs (LazyBinding _ _ (Lf _ binds _ _)) =
            S.unions <$> mapM (checkFV svs . snd) binds
        bindingFVs (BoxBinding _ _ v) = checkFV svs v
        bindingFVs (Reuse _ _ _ caps) =
            S.unions <$> mapM (checkFV svs . snd) caps

        extractName :: Binding -> Var
        extractName (LazyBinding _ v _) = baseVar v
        extractName (BoxBinding _ v _) = v
        extractName (Reuse v _ _ _) = v
        
        allNames :: S.HashSet Var
        allNames = S.fromList (map extractName bindings)

    -- let extractName (LazyBinding _ v _) = S.singleton (baseVar v)
    --     extractName (BoxBinding _ v _) = S.singleton v
    --     extractName (Reuse v _ _) = S.singleton v
    --     -- extractName (EagerBinding _ v _) = S.singleton (baseVar v)
    --     findBindFVs (LazyBinding _ _ (Lf _ _ binds body)) = do
    --         local (bound %~ S.union (S.fromList (map (baseVar . snd) binds))) $ do
    --             case body of
    --               LazyOnly expr -> findFVs svs expr
    --               Both strict lazy -> do
    --                   strictFVs <- findFVs svs strict
    --                   lazyFVs <- findFVs svs lazy
    --                   pure (S.union strictFVs lazyFVs)
    --     findBindFVs (BoxBinding _ _ v) = checkFV svs v
    --     findBindFVs (Reuse {}) = pure S.empty
    --     -- findBindFVs (EagerBinding _ _ e) = findFVs e
    --     allNames = S.unions (map extractName bindings)
    --  in local (bound %~ S.union allNames) $ do
    --         bindingFVs <- mapM findBindFVs bindings
    --         bodyFVs <- findFVs svs body
    --         pure (S.unions (bodyFVs:bindingFVs))

findFVs svs (Case disc branches) = do
    discFVs <- findFVs svs disc
    let findBranch (Alt _ pat expr) = local (bound %~ S.union (namesInPattern pat)) $ findFVs svs expr
    branchFVs <- NE.toList <$> mapM findBranch branches
    pure (S.unions (discFVs:branchFVs))

findFVs svs (Application _ fun args) = do
    fnFVs <- checkFV svs fun
    argFVs <- mapM (checkAtom svs) args
    pure (S.unions (fnFVs:argFVs))

findFVs svs (PrimApp _ _ args) = S.unions <$> mapM (checkAtom svs) args

findFVs svs (ConsApp _ _ args) = S.unions <$> mapM (checkAtom svs) args

findFVs svs (PackedTuple ts) = S.unions <$> mapM (checkAtom svs) ts

findFVs svs (Projector _ _ v) = checkFV svs v

findFVs _ Error = pure S.empty

checkAtom :: S.HashSet Var -> Atom -> Translator (S.HashSet (Bool, Var))
checkAtom svs (Var v) = checkFV svs v
checkAtom _ _ = pure S.empty

checkFV :: S.HashSet Var -> Var -> Translator (S.HashSet (Bool, Var))
checkFV svs v = do
    isBound <- asks (S.member v . (^. bound))
    let strict = S.member v svs
    if isBound
       then pure S.empty
       else pure (S.singleton (strict, v))

namesInPattern :: Pattern -> S.HashSet Var
namesInPattern (VarPattern v) = S.singleton (baseVar v)
namesInPattern (LitPattern _) = S.empty
namesInPattern (ConsPattern _ ps) = S.unions (map namesInPattern ps)
namesInPattern (TuplePattern ts) = S.unions (map namesInPattern ts)

addTags :: T.TypedExpr -> TaggedTExpr
addTags e = evalState (unfoldFixM tagExpr e) 0
    where
        tagExpr :: T.TypedExpr -> State Tag (TaggedTExprF T.TypedExpr)
        tagExpr expr = do
            tagVal <- get
            modify (+1)
            pure (Tagged (unFix expr) tagVal)

convertAST :: T.StaticContext -> T.MultiplicityPoset -> T.TypedExpr -> CodegenExpr
convertAST staticContext poset expr =
    let initCtx = TranslatorContext
            { _idMap = M.empty
            , _bound = S.empty
            , _evalContext = (True, True)
            }
        initState = TranslatorState
            { _nextVar = 0
            , _strictness = M.empty
            , _builtBindings = M.empty
            , _builtPatterns = M.empty
            }
     in evalState (runReaderT (convert (addTags expr)) initCtx) initState
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

        convert :: TaggedTExpr -> Translator CodegenExpr
        convert letExpr@(LetT _ bindings body) = do
            rel <- relevantCtx
            (makeBinds, ids) <- createBindings rel bindings
            local (idMap %~ M.union ids) $ do
                (binds, projection) <- makeBinds
                graph <- buildOrderGraph binds
                cvtBody <- convert body
                pure (buildLetPath (projection cvtBody) (stronglyConnComp graph))
            where
                createBindings :: Bool -> [T.TypedLetBindingF TaggedTExpr]
                               -> Translator (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                createBindings _ [] = pure (pure ([], id), M.empty)
                createBindings rel ((T.TypedLetBinding mul pat expr):binds)
                    -- All strict patterns should add a case expression to the binding body
                    | isRelevant mul && rel = do
                        (p, patIds) <- convertPattern (tag expr) pat
                        affine <- affineCtx
                        let addedNameSet = M.keysSet patIds
                            caseExpr = do
                                cvtExpr <- updateContext $
                                    local (idMap %~ M.filterWithKey (\k _ -> not (k `S.member` addedNameSet))) $ convert expr
                                pure (Case cvtExpr . NE.singleton . Alt (affine && isAffine mul) p)
                        (restBinds, ids) <- createBindings rel binds
                        pure (addPatternMatch caseExpr restBinds, M.union (M.map (\tv -> (isRelevant mul, baseVar tv)) patIds) ids)
                    -- Lazy patterns which can be directly projected from generate
                    -- non strict thunks and projectors
                    | directProjection pat = do
                        (thunk, thunkVar) <- makeThunk updateContext (Just pat) expr
                        (restBinds, ids) <- createBindings rel binds
                        case pat of
                          T.VariablePattern t name -> do
                              pure (addBinding thunk restBinds, M.insert name (isRelevant mul, thunkVar) ids)
                          T.LiteralPattern (P.TupleLiteral ts) -> do
                              projVars <- forM ts $ \(T.VariablePattern t name) -> do
                                  projVar <- freshName
                                  pure (name, TV projVar (typeToTType t))
                              foldM (addProjector thunkVar)
                                  (addBinding thunk restBinds, ids) (zip projVars [0..])
                          _ -> error "Direct projection failure"
                    -- Non-trivial patterns generate non strict thunks which
                    -- extract values and non strict projectors
                    | otherwise = do
                        bindVar <- freshName
                        (p, patIds) <- convertPattern (tag expr) pat
                        (restBinds, ids) <- createBindings rel binds
                        let patList = M.toList patIds
                            extractExpr = do
                                let name = "__thunk_" ++ show (tag expr)
                                lf <- updateContext $ convertLambdas expr
                                case lf of
                                  Left (Lf update caps args body) ->
                                      let tupleType = Tuple (map (varType . snd) patList)
                                          -- TODO: Free parameter is conditionally true -- maybe we need to pass
                                          -- a monadic continuation into convertLambdas with what to do with the result?
                                          -- Default -- pure, projection -- lookup if affine to decide to free
                                          matcher = NE.singleton (Alt False p (PackedTuple (map (Var . baseVar . snd) patList)))
                                          extractor = mapBodies (`Case` matcher) body
                                       in pure (LazyBinding name (TV bindVar tupleType) (Lf update caps args extractor))
                                  Right caps -> pure (Reuse bindVar name (tag expr) caps)
                            binds' = addBinding extractExpr restBinds
                        foldM (addProjector bindVar) (binds', ids) (zip patList [0..])
                    where
                        addProjector :: Var
                                     -> (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                                     -> ((P.Identifier, TypedVar), Int)
                                     -> Translator (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                        addProjector var (binds, ids) ((nameId@(P.I name), projVar), index) = do
                            let lf = Lf U [(False, var)] [] (LambdaBody
                                                                        (Just (Projector (True, True) index var))
                                                                        (Just (Projector (True, False) index var))
                                                                        (Just (Projector (False, True) index var))
                                                                        (Just (Projector (False, False) index var)))
                                binding = LazyBinding name projVar lf
                                binds' = addBinding (pure binding) binds
                                ids' = M.insert nameId (isRelevant mul, baseVar projVar) ids
                            pure (binds', ids')

                        updateContext :: Translator a -> Translator a
                        updateContext = withContext (&& isRelevant mul) (&& isAffine mul)

                nonDataHolder :: T.Type -> Bool
                nonDataHolder (T.FunctionType _ _ to) = nonDataHolder to
                nonDataHolder (T.Ground (P.I "Int")) = True
                nonDataHolder (T.Ground (P.I "Bool")) = True
                nonDataHolder _ = False

                addBinding :: Translator Binding
                           -> Translator ([Binding], CodegenExpr -> CodegenExpr)
                           -> Translator ([Binding], CodegenExpr -> CodegenExpr)
                addBinding getBind getBinds = do
                    bind <- getBind
                    (binds, fn) <- getBinds
                    pure (bind : binds, fn)

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

                buildOrderGraph :: [Binding] -> Translator [(Binding, Integer, [Integer])]
                buildOrderGraph [] = pure []
                buildOrderGraph (bind@(LazyBinding _ v (Lf _ caps _ _)):bs) = do
                    let node = (bind, (varID . baseVar) v, map (varID . snd) caps)
                    (node:) <$> buildOrderGraph bs
                buildOrderGraph (bind@(BoxBinding _ v v'):bs) = do
                    let node = (bind, varID v, [varID v'])
                    (node:) <$> buildOrderGraph bs
                buildOrderGraph (bind@(Reuse v _ tag caps):bs) = do
                    let node = (bind, varID v, map (varID . snd) caps)
                    (node:) <$> buildOrderGraph bs

                buildLetPath :: CodegenExpr -> [SCC Binding] -> CodegenExpr
                buildLetPath base [] = base
                buildLetPath base (AcyclicSCC v:sccs) = Let [v] (buildLetPath base sccs)
                buildLetPath base (CyclicSCC vs:sccs) = Let vs (buildLetPath base sccs)

        convert (CaseT _ mul disc branches) = do
            -- The discriminator is only GU if the expression is GU and the discriminator
            -- is relevant
            cvtDisc <- withContext (&& isRelevant mul) (&& isAffine mul) (convert disc)
            -- Branches are GU if the expression is GU
            cvtBranches <- mapM cvtBranch branches
            pure (Case cvtDisc cvtBranches)
            where
                cvtBranch :: T.TypedCaseBranchF TaggedTExpr -> Translator Alternative
                cvtBranch (T.TypedCaseBranch pat branch) = do
                    (p, ids) <- convertPattern (tag branch) pat
                    cvtBranch <- local (idMap %~ M.union (M.map (\tv -> (isRelevant mul || isVarPattern pat, baseVar tv)) ids)) $ convert branch
                    affine <- affineCtx
                    pure (Alt (affine && isAffine mul) p cvtBranch)

        convert (ApplicationT _ fun arg) = do
            let (T.FunctionType _ (T.Arrow mul) _) = typeof fun
            collectArgs fun [(mul, arg)]
            where
                collectArgs :: TaggedTExpr -> [(Multiplicity, TaggedTExpr)] -> Translator CodegenExpr
                collectArgs (ApplicationT _ f a) args =
                    let (T.FunctionType _ (T.Arrow mul) _) = typeof f
                     in collectArgs f ((mul, a):args)
                collectArgs var@(VariableT t name@(P.I rawName)) args
                    | isJust (B.getPrimitive name) = do
                        rel <- relevantCtx
                        aff <- affineCtx
                        liftArgs (map (\(m, e) -> (rel && isRelevant m, m, e)) args) (PrimApp aff (fromJust (B.getPrimitive name)))
                    | rawName == "MkInt#" = do
                        aff <- affineCtx
                        liftArgs (map (\(_, e) -> (True, MAtom P.Linear, e)) args) (ConsApp aff name)
                    | rawName == "MkReal#" = do
                        aff <- affineCtx
                        liftArgs (map (\(_, e) -> (True, MAtom P.Linear, e)) args) (ConsApp aff name)
                    | M.member name (staticContext ^. T.dataConstructors) = do
                        aff <- affineCtx
                        liftArgs (map (\(_, expr) -> (False, MAtom P.Normal, expr)) args) (ConsApp aff name)
                    | otherwise = do
                        funVar <- lookupVar name
                        rel <- relevantCtx
                        aff <- affineCtx
                        case funVar of
                          Just v -> do
                              argStrictness <- gets ((M.! v) . (^. strictness))
                              liftArgs (zipWith (\s (m, e) -> (s && rel, m, e)) argStrictness args) (Application (rel, aff) v)
                          Nothing -> pure Error
                collectArgs expr args = do
                    -- Innermost function is GU if the application is GU
                    funExpr <- convert expr
                    rel <- relevantCtx
                    case funExpr of
                      Let binds (Application strict funVar []) -> do
                          liftArgs (map (\(m, e) -> (rel && isRelevant m, m, e)) args) (Let binds . Application strict funVar)
                      _ -> do
                          let funTy = typeToTType (typeof expr)
                          funVar <- freshName
                          affine <- affineCtx
                          let alt = Alt affine (VarPattern (TV funVar funTy)) . Application (rel, affine) funVar
                              caseExpr = Case funExpr . NE.singleton . alt
                          liftArgs (map (\(m, e) -> (rel && isRelevant m, m, e)) args) caseExpr

                liftArgs :: [(Bool, Multiplicity, TaggedTExpr)] -> ([Atom] -> CodegenExpr) -> Translator CodegenExpr
                liftArgs args app = do
                    (argVars, binds, projectors) <- unzip3 <$> mapM (\(s, m, e) -> liftFuncArg s m e) args
                    let combinedProjector = foldr (.) id projectors
                    pure (Let (catMaybes binds) (combinedProjector (app argVars)))

        convert lam@(LambdaT t _ _ _) = do
            rel <- relevantCtx
            aff <- relevantCtx
            (mkBind, var) <- makeThunk id Nothing lam
            bind <- mkBind
            -- modify (builtBindings %~ M.insert (tag lam) ([bind], ))
            pure (Let [bind] (Application (rel, aff) var []))
            -- let lambdaTy = ttype t
            -- lambdaName <- freshName
            -- bind <- LazyBinding Nothing (TV lambdaName lambdaTy) <$> convertLambdas lam
            -- pure (Let [bind] (Application lambdaName []))

        convert (VariableT t name)
            | isJust (B.getPrimitive name) = do
                aff <- affineCtx
                pure (PrimApp aff (fromJust (B.getPrimitive name)) [])
            | M.member name (staticContext ^. T.dataConstructors) = do
                aff <- affineCtx
                pure (ConsApp aff name [])
            | otherwise = do
                rel <- relevantCtx
                aff <- affineCtx
                funVar <- lookupVar name
                case funVar of
                  Just v -> pure (Application (rel, aff) v [])
                  Nothing -> pure Error

        convert (TupleT t ts) = do
            rel <- relevantCtx
            (argVars, binds, projectors) <- unzip3 <$> mapM (liftFuncArg rel (MAtom P.Linear)) ts
            let combinedProjector = foldr (.) id projectors
            pure (Let (catMaybes binds) (combinedProjector (PackedTuple argVars)))

        convert (LiteralT t lit) = do
            affine <- affineCtx
            convertLit affine lit
            where
                convertLit :: Bool -> PrimitiveLiteral -> Translator CodegenExpr
                convertLit affine (IntLit i) = pure (ConsApp affine (P.I "MkInt#") [Lit (IntLit i)])
                convertLit affine (RealLit r) = pure (ConsApp affine (P.I "MkReal#") [Lit (RealLit r)])

        nameForPattern :: T.Pattern -> Maybe String
        nameForPattern (T.VariablePattern _ (P.I name)) = Just name
        nameForPattern _ = Nothing

        convertPattern :: Tag -> T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
        convertPattern t pat = do
            prebuilt <- gets (M.lookup t . (^. builtPatterns))
            case prebuilt of
              Just p -> pure p
              Nothing -> do
                  p <- cvtPat pat
                  modify (builtPatterns %~ M.insert t p)
                  pure p
            where   
                cvtPat :: T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
                cvtPat (T.VariablePattern t name) = do
                    v <- freshName
                    pure (VarPattern (TV v (typeToTType t)), M.singleton name (TV v (typeToTType t)))
                cvtPat (T.ConstructorPattern name ps) = do
                    (ps', maps) <- mapAndUnzipM cvtPat ps
                    pure (ConsPattern name ps', M.unions maps)
                cvtPat (T.LiteralPattern lit) = convertLitPattern lit
                    where
                        convertLitPattern :: P.Literal T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
                        convertLitPattern (P.IntLiteral i) = pure (ConsPattern (P.I "MkInt#") [LitPattern (IntLit i)], M.empty)
                        convertLitPattern (P.RealLiteral r) = pure (ConsPattern (P.I "MkReal#") [LitPattern (RealLit r)], M.empty)
                        convertLitPattern (P.ListLiteral ps) = do
                            (ps', maps) <- mapAndUnzipM cvtPat ps
                            pure (foldr (\x xs -> ConsPattern (P.I "::") [x, xs]) (ConsPattern (P.I "[]") []) ps', M.unions maps)
                        convertLitPattern (P.TupleLiteral ps) = do
                            (ps', maps) <- mapAndUnzipM cvtPat ps
                            pure (TuplePattern ps', M.unions maps)

        makeThunk :: (forall a. Translator a -> Translator a) -> Maybe T.Pattern -> TaggedTExpr -> Translator (Translator Binding, Var)
        makeThunk updateContext pat expr = do
            bindVar <- freshName
            modify (strictness %~ M.insert bindVar (getArgStrictness (typeof expr)))
            let name' = fromMaybe ("__thunk_" ++ show (tag expr)) (pat >>= nameForPattern)
                binding = do
                    -- lf <- local (bound %~ S.insert bindVar) $ convertLambdas expr
                    lf <- updateContext $ convertLambdas expr
                    case lf of
                      Left lambdaForm -> pure (LazyBinding name' (TV bindVar (typeToTType (typeof expr))) lambdaForm)
                      Right caps -> pure (Reuse bindVar name' (tag expr) caps)
            pure (binding, bindVar)

        convertLambdas :: TaggedTExpr -> Translator (Either LambdaForm [(Bool, Var)])
        convertLambdas lam@(LambdaT {}) = do
            prebuilt <- gets (M.lookup (tag lam) . (^. builtBindings))
            case prebuilt of
              Just (Lf _ caps _ _) -> pure (Right caps)
              Nothing -> do
                  ((args, body), rebound) <- rebindCapturesIn $ collectLambdas' 0 [] lam
                  let boundArgs = S.fromList (map (baseVar . snd) args)
                  fvs <- maybe (pure S.empty) (local (bound %~ S.union boundArgs) . findFVs rebound) (firstBody body)
                  -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
                  -- If a relevant variable is captured, it always must be put into a thunk. Therefore,
                  -- we can lift this thunk out of the lambda form. That way, all captures are always
                  -- thunks and we avoid the exponential code generation problem.
                  -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
                  let lambdaForm = Lf N (S.toList fvs) args body
                  modify (builtBindings %~ M.insert (tag lam) lambdaForm)
                  pure (Left lambdaForm)
            where
                collectLambdas' :: Int -> [(Var, T.Pattern, Multiplicity, Tag)] -> TaggedTExpr
                                -> Translator ([(Bool, TypedVar)], LambdaBody)
                collectLambdas' depth toMatch (LambdaT (T.FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
                    varName <- freshName
                    modify (strictness %~ M.insert varName (getArgStrictness from))
                    (vs, expr) <- local (idMap %~ M.insert name (isRelevant mul, varName)) $ collectLambdas' (depth + 1) toMatch body
                    pure ((isRelevant mul && not (isFunctionType from), TV varName (typeToTType from)):vs, expr)
                collectLambdas' depth toMatch (LambdaT (T.FunctionType from _ _) mul pat body) = do
                    varName <- freshName
                    modify (strictness %~ M.insert varName (getArgStrictness from))
                    (vs, expr) <- collectLambdas' (depth + 1) ((varName, pat, mul, tag body):toMatch) body
                    pure ((isRelevant mul && not (isFunctionType from), TV varName (typeToTType from)):vs, expr)
                collectLambdas' depth toMatch expr = do
                    linearBase <- withContext (const True) (const True) $ buildCases (reverse toMatch)
                    relevantBase <- withContext (const True) (const False) $ buildCases (reverse toMatch)
                    affineBase <- withContext (const False) (const True) $ buildCases (reverse toMatch)
                    normalBase <- withContext (const False) (const False) $ buildCases (reverse toMatch)
                    pure ([], LambdaBody (Just linearBase) (Just relevantBase) (Just affineBase) (Just normalBase))
                    where
                        buildCases :: [(Var, T.Pattern, Multiplicity, Tag)] -> Translator CodegenExpr
                        buildCases [] = convert expr
                        buildCases ((v, pat, mul, tag):rest) = do
                            rel <- relevantCtx
                            affine <- affineCtx
                            (p, ids) <- convertPattern tag pat
                            local (idMap %~ M.union (M.map (\tv -> (isRelevant mul, baseVar tv)) ids)) $ do
                                -- baseExpr <- (if isAffine mul then Free v else id) <$> buildCases rest
                                baseExpr <- buildCases rest
                                pure (Case (Application (rel && isRelevant mul, affine && isAffine mul) v [])
                                           (NE.singleton (Alt (affine && isAffine mul) p baseExpr)))

        convertLambdas expr = do
            prebuilt <- gets (M.lookup (tag expr) . (^. builtBindings))
            case prebuilt of
              Just (Lf _ caps _ _) -> pure (Right caps)
              Nothing -> do
                  (body, rebound) <- rebindCapturesIn $ do
                      l <- withContext (const True) (const True) $ convert expr
                      r <- withContext (const True) (const False) $ convert expr
                      a <- withContext (const False) (const True) $ convert expr
                      n <- withContext (const False) (const False) $ convert expr
                      pure (LambdaBody (Just l) (Just r) (Just a) (Just n))
                  fvs <- maybe (pure S.empty) (findFVs rebound) (firstBody body)
                  let lambdaForm = Lf U (S.toList fvs) [] body
                  modify (builtBindings %~ M.insert (tag expr) lambdaForm)
                  pure (Left lambdaForm)

        rebindCapturesIn :: Translator a -> Translator (a, S.HashSet Var)
        rebindCapturesIn env = do
            boundIds <- asks (^. idMap)
            rel <- relevantCtx
            let (rebound, vars) = runState (mapM (rebind rel) boundIds) S.empty
            (, vars) <$> local (idMap .~ rebound) env
            where
                rebind :: Bool -> (Bool, Var) -> State (S.HashSet Var) (Bool, Var)
                rebind True (True, v) = modify (S.insert v) >> pure (False, v)
                rebind _ (_, v) = pure (False, v)

        lookupVar :: P.Identifier -> Translator (Maybe Var)
        lookupVar name = asks ((snd <$>) . M.lookup name . (^. idMap))

        lookupStrictness :: P.Identifier -> Translator Bool
        lookupStrictness name = asks (fst . (M.! name) . (^. idMap))

        liftFuncArg :: Bool -> Multiplicity -> TaggedTExpr
                    -> Translator (Atom, Maybe Binding, CodegenExpr -> CodegenExpr)
        liftFuncArg strict mul var@(VariableT t name)
            -- | not (M.member name (staticContext ^. T.defaultFunctions))
            | not (M.member name (staticContext ^. T.dataConstructors)) = do
                rel <- relevantCtx
                aff <- affineCtx
                argVar <- fromJust <$> lookupVar name
                if strict
                   then do
                       matchVar <- freshName
                       -- We can always mark this as false -- the pattern is just a variable
                       let alt = Alt False (VarPattern (TV matchVar (typeToTType t)))
                           matcher = Case (Application (True, aff) argVar []) . NE.singleton . alt
                       pure (Var matchVar, Nothing, matcher)
                   else do
                       strictVar <- lookupStrictness name
                       if strictVar && rel
                          then do
                              boxVar <- freshName
                              let bind = BoxBinding ("__thunk_" ++ show (tag var)) boxVar argVar
                              pure (Var boxVar, Nothing, Let [bind])
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
        liftFuncArg strict mul arg = do
            if strict
               then do
                   cvtArg <- withContext (&& isRelevant mul) (&& isAffine mul) $ convert arg
                   matchVar <- freshName
                   let alt = Alt False (VarPattern (TV matchVar (typeToTType (typeof arg))))
                       matcher = Case cvtArg . NE.singleton . alt
                   pure (Var matchVar, Nothing, matcher)
               else do
                   cvtArg <- withRelevant (const False) $ convertLambdas arg
                   bindVar <- freshName
                   let name = "__thunk_" ++ show (tag arg) 
                       binding = case cvtArg of
                                   Left lf -> LazyBinding name (TV bindVar (typeToTType (typeof arg))) lf
                                   Right caps -> Reuse bindVar name (tag arg) caps
                   pure (Var bindVar, Just binding, id)

        isRelevant :: Multiplicity -> Bool
        isRelevant mul = P.leq mul (T.MAtom P.Relevant) poset

        isAffine :: Multiplicity -> Bool
        isAffine mul = P.leq mul (T.MAtom P.Affine) poset

        relevantCtx :: Translator Bool
        relevantCtx = asks (fst . (^. evalContext))

        affineCtx :: Translator Bool
        affineCtx = asks (snd . (^. evalContext))

        withRelevant :: (Bool -> Bool) -> Translator a -> Translator a
        withRelevant update = local (evalContext . _1 %~ update)

        withAffine :: (Bool -> Bool) -> Translator a -> Translator a
        withAffine update = local (evalContext . _2 %~ update)

        withContext :: (Bool -> Bool) -> (Bool -> Bool) -> Translator a -> Translator a
        withContext updateRel updateAff = withRelevant updateRel . withAffine updateAff

        isLambda :: T.TypedExpr -> Bool
        isLambda (T.Lambda {}) = True
        isLambda _ = False

        isFunctionType :: T.Type -> Bool
        isFunctionType (T.FunctionType {}) = True
        isFunctionType _ = False

        isVarPattern :: T.Pattern -> Bool
        isVarPattern (T.VariablePattern {}) = True
        isVarPattern _ = False

        getArgStrictness :: T.Type -> [Bool]
        getArgStrictness (T.FunctionType from (T.Arrow mul) to) =
            (isRelevant mul && not (isFunctionType from)) : getArgStrictness to
        getArgStrictness _ = []

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

