{-# LANGUAGE TemplateHaskell, DeriveGeneric, TupleSections, PatternSynonyms, RankNTypes #-}
module Compiler.Translate where

-- Translator mapping STFL (typed) source code into STFL-Core

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
    | Application TranslateType (Bool, Bool) Var [Atom]
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
prettyPrintCodegenExpr (Application _ mul fun args) =
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

data UpdateFlag = Updatable | NonUpdatable | FreeAfterUse
    deriving Eq

instance Show UpdateFlag where
    show Updatable = "u"
    show NonUpdatable = "n"
    show FreeAfterUse = "f"

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

type IdMap = M.HashMap P.Identifier ((Bool, Bool), Var)

data TranslatorContext = TranslatorContext
    { _idMap :: IdMap
    , _bound :: S.HashSet Var
    , _evalContext :: (Bool, Bool)
    , _lockAffine :: Bool
    }

makeLenses ''TranslatorContext

data TranslatorState = TranslatorState
    { _nextVar :: Integer
    , _strictness :: M.HashMap Var [Bool]
    , _builtBindings :: M.HashMap Tag LambdaForm
    , _builtPatterns :: M.HashMap (Tag, P.Identifier) Var
    }

makeLenses ''TranslatorState

type Translator a = ReaderT TranslatorContext (State TranslatorState) a

findFVs :: S.HashSet Var -> CodegenExpr -> Translator (S.HashSet (Bool, Var))
findFVs svs (Let bindings body) = do
    local (bound %~ S.union allNames) $ do
        bindFVs <- S.unions <$> mapM bindingFVs bindings
        bodyFVs <- findFVs svs body
        pure (S.union bodyFVs bindFVs)
    where
        bindingFVs :: Binding -> Translator (S.HashSet (Bool, Var))
        bindingFVs (LazyBinding _ _ (Lf _ caps _ _)) =
            S.unions <$> mapM (checkFV svs . snd) caps
        bindingFVs (BoxBinding _ _ v) = checkFV svs v
        bindingFVs (Reuse _ _ _ caps) =
            S.unions <$> mapM (checkFV svs . snd) caps

        extractName :: Binding -> Var
        extractName (LazyBinding _ v _) = baseVar v
        extractName (BoxBinding _ v _) = v
        extractName (Reuse v _ _ _) = v
        
        allNames :: S.HashSet Var
        allNames = S.fromList (map extractName bindings)

findFVs svs (Case disc branches) = do
    discFVs <- findFVs svs disc
    let findBranch (Alt _ pat expr) = local (bound %~ S.union (namesInPattern pat)) $ findFVs svs expr
    branchFVs <- NE.toList <$> mapM findBranch branches
    pure (S.unions (discFVs:branchFVs))

findFVs svs (Application _ _ fun args) = do
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

findRecursiveValues :: [T.TypedLetBindingF TaggedTExpr] -> S.HashSet Tag
findRecursiveValues binds =
    let nodes = foldr addBindNodes [] binds
        sccs = stronglyConnComp nodes
     in S.unions (map findRecursive sccs)
    where
        findRecursive :: SCC (Maybe Tag) -> S.HashSet Tag
        findRecursive (AcyclicSCC _) = S.empty
        findRecursive (CyclicSCC cycle) = S.fromList (catMaybes cycle)

        addBindNodes :: T.TypedLetBindingF TaggedTExpr
                     -> [(Maybe Tag, P.Identifier, [P.Identifier])]
                     -> [(Maybe Tag, P.Identifier, [P.Identifier])]
        addBindNodes (T.TypedLetBinding _ pat body) nodes =
            let appear = foldFix appearingNames body
                patNames = namesInPattern pat
             in foldr (addPatternNodes (tag body <$ ignoreFunctionPattern pat) (S.toList appear)) nodes patNames
            where
                ignoreFunctionPattern :: T.Pattern -> Maybe ()
                ignoreFunctionPattern (T.VariablePattern (T.FunctionType {}) _) = Nothing
                ignoreFunctionPattern p = Just ()

        addPatternNodes :: Maybe Tag -> [P.Identifier] -> P.Identifier
                        -> [(Maybe Tag, P.Identifier, [P.Identifier])]
                        -> [(Maybe Tag, P.Identifier, [P.Identifier])]
        addPatternNodes patNode appear name =
            let node = (patNode, name, appear)
             in (node:)

        namesInPattern :: T.Pattern -> S.HashSet P.Identifier
        namesInPattern (T.VariablePattern _ name) = S.singleton name
        namesInPattern (T.ConstructorPattern _ ps) = S.unions (map namesInPattern ps)
        namesInPattern (T.LiteralPattern lit) = namesInLit lit
            where
                namesInLit :: P.Literal T.Pattern -> S.HashSet P.Identifier
                namesInLit (P.ListLiteral ls) = S.unions (map namesInPattern ls)
                namesInLit (P.TupleLiteral ts) = S.unions (map namesInPattern ts)
                namesInLit _ = S.empty
        
        appearingNames :: TaggedTExprF (S.HashSet P.Identifier) -> S.HashSet P.Identifier
        appearingNames (Tagged (T.Let_ _ binds body) _) =
            let allBoundNames = S.unions (map extractPatternNames binds)
             in S.difference (S.unions (body : map extractBindBody binds)) allBoundNames
            where
                extractPatternNames :: T.TypedLetBindingF (S.HashSet P.Identifier) -> S.HashSet P.Identifier
                extractPatternNames (T.TypedLetBinding _ pat body) = namesInPattern pat

                extractBindBody :: T.TypedLetBindingF (S.HashSet P.Identifier) -> S.HashSet P.Identifier
                extractBindBody (T.TypedLetBinding _ _ body) = body
        appearingNames (Tagged (T.Case_ _ _ disc branches) _) =
            S.unions (disc : map (\(T.TypedCaseBranch _ body) -> body) (NE.toList branches))
        appearingNames (Tagged (T.Application_ _ fun arg) _) = S.union fun arg
        appearingNames (Tagged (T.Lambda_ _ _ pat body) _) = S.difference body (namesInPattern pat)
        appearingNames (Tagged (T.Variable_ _ name) _) = S.singleton name
        appearingNames (Tagged (T.Tuple_ _ ts) _) = S.unions ts
        appearingNames (Tagged (T.Literal_ _ _) _) = S.empty

convertAST :: T.StaticContext -> T.MultiplicityPoset -> T.TypedExpr -> CodegenExpr
convertAST staticContext poset expr =
    let initCtx = TranslatorContext
            { _idMap = M.empty
            , _bound = S.empty
            , _evalContext = (True, True)
            , _lockAffine = False
            }
        initState = TranslatorState
            { _nextVar = 0
            , _strictness = M.empty
            , _builtBindings = M.empty
            , _builtPatterns = M.empty
            }
     in evalState (runReaderT (convert (addTags expr)) initCtx) initState
    where

        convert :: TaggedTExpr -> Translator CodegenExpr
        convert letExpr@(LetT _ bindings body) = do
            let recursiveVals = findRecursiveValues bindings
            rel <- relevantCtx
            (makeBinds, ids) <- createBindings recursiveVals rel bindings
            local (idMap %~ M.union ids) $ do
                (binds, projection) <- makeBinds
                graph <- buildOrderGraph binds
                cvtBody <- convert body
                pure (buildLetPath (projection cvtBody) (stronglyConnComp graph))
            where
                createBindings :: S.HashSet Tag -> Bool -> [T.TypedLetBindingF TaggedTExpr]
                               -> Translator (Translator ([Binding], CodegenExpr -> CodegenExpr), IdMap)
                createBindings recs _ [] = pure (pure ([], id), M.empty)
                createBindings recs rel ((T.TypedLetBinding mul pat expr):binds)
                    -- All strict patterns should add a case expression to the binding body
                    | isRelevant mul && rel = do
                        (p, patIds) <- convertPattern (tag expr) pat
                        affine <- affineCtx
                        let addedNameSet = M.keysSet patIds
                            caseExpr = do
                                cvtExpr <- updateContext $ lockAffineOnPath (tag expr `S.member` recs) $
                                    local (idMap %~ M.filterWithKey (\k _ -> not (k `S.member` addedNameSet))) $ convert expr
                                pure (Case cvtExpr . NE.singleton . Alt (affine && isAffine mul) p)
                        (restBinds, ids) <- createBindings recs rel binds
                        pure (addPatternMatch caseExpr restBinds, M.union (M.map (\tv -> ((isVarPattern pat, isAffine mul), baseVar tv)) patIds) ids)
                    -- Lazy patterns which can be directly projected from generate
                    -- non strict thunks and projectors
                    | directProjection pat = do
                        (thunk, thunkVar) <- makeThunk (tag expr `S.member` recs) updateContext (Just pat) expr
                        (restBinds, ids) <- createBindings recs rel binds
                        case pat of
                          T.VariablePattern t name -> do
                              pure (addBinding thunk restBinds, M.insert name ((isRelevant mul, isAffine mul), thunkVar) ids)
                          T.LiteralPattern (P.TupleLiteral ts) -> do
                              projVars <- forM ts $ \(T.VariablePattern t name) -> do
                                  prebuilt <- gets (M.lookup (tag expr, name) . (^. builtPatterns))
                                  projVar <- maybe freshName pure prebuilt
                                  modify (builtPatterns %~ M.insert (tag expr, name) projVar)
                                  pure (name, TV projVar (typeToTType t))
                              foldM (addProjector thunkVar)
                                  (addBinding thunk restBinds, ids) (zip projVars [0..])
                          _ -> error "Direct projection failure"
                    -- Non-trivial patterns generate non strict thunks which
                    -- extract values and non strict projectors
                    | otherwise = do
                        bindVar <- freshName
                        (p, patIds) <- convertPattern (tag expr) pat
                        (restBinds, ids) <- createBindings recs rel binds
                        let patList = M.toList patIds
                            extractExpr = do
                                let name = "__thunk_" ++ show (tag expr)
                                lf <- updateContext $ lockAffineOnPath (tag expr `S.member` recs) $ convertLambdas expr
                                case lf of
                                  Left (Lf update caps args body) ->
                                      let tupleType = Tuple (map (varType . snd) patList)
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
                            affine <- affineCtx
                            let flag
                                    | affine && isAffine mul = Updatable
                                    | otherwise = Updatable
                                lf = Lf flag [(False, var)] [] (LambdaBody
                                                                        (Just (Projector (True, True) index var))
                                                                        (Just (Projector (True, False) index var))
                                                                        (Just (Projector (False, True) index var))
                                                                        (Just (Projector (False, False) index var)))
                                binding = LazyBinding name projVar lf
                                binds' = addBinding (pure binding) binds
                                ids' = M.insert nameId ((isRelevant mul, isAffine mul), baseVar projVar) ids
                            pure (binds', ids')

                        updateContext :: Translator a -> Translator a
                        updateContext = withContext (&& isRelevant mul) (&& isAffine mul && not (tag expr `S.member` recs))

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
                    cvtBranch <- local (idMap %~ M.union (M.map (\tv -> ((isRelevant mul && isVarPattern pat, isAffine mul), baseVar tv)) ids)) $ convert branch
                    affine <- affineCtx
                    pure (Alt (affine && isAffine mul) p cvtBranch)

        convert (ApplicationT t fun arg) = do
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
                        liftArgs (map (\(m, expr) -> (False, m, expr)) args) (ConsApp aff name)
                    | otherwise = do
                        funVar <- lookupVar name
                        rel <- relevantCtx
                        aff <- affineCtx
                        case funVar of
                          Just v -> do
                              argStrictness <- gets ((M.! v) . (^. strictness))
                              liftArgs (zipWith (\s (m, e) -> (s && rel, m, e)) argStrictness args) (Application (typeToTType t) (rel, aff) v)
                          Nothing -> pure Error
                collectArgs expr args = do
                    -- Innermost function is GU if the application is GU
                    funExpr <- convert expr
                    rel <- relevantCtx
                    case funExpr of
                      Let binds (Application _ strict funVar []) -> do
                          liftArgs (map (\(m, e) -> (rel && isRelevant m, m, e)) args) (Let binds . Application (typeToTType t) strict funVar)
                      _ -> do
                          let funTy = typeToTType (typeof expr)
                          funVar <- freshName
                          affine <- affineCtx
                          let alt = Alt affine (VarPattern (TV funVar funTy)) . Application (typeToTType t) (rel, affine) funVar
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
            (mkBind, var) <- makeThunk False id Nothing lam
            bind <- mkBind
            pure (Let [bind] (Application (typeToTType t) (rel, aff) var []))

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
                  Just v -> pure (Application (typeToTType t) (rel, aff) v [])
                  Nothing -> pure Error

        convert (TupleT t ts) = do
            (argVars, binds, projectors) <- unzip3 <$> mapM (liftFuncArg False (MAtom P.Linear)) ts
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
        convertPattern tag = cvtPat
            where   
                cvtPat :: T.Pattern -> Translator (Pattern, M.HashMap P.Identifier TypedVar)
                cvtPat (T.VariablePattern t name) = do
                    prebuilt <- gets (M.lookup (tag, name) . (^. builtPatterns))
                    v <- maybe freshName pure prebuilt
                    modify (builtPatterns %~ M.insert (tag, name) v)
                    modify (strictness %~ M.insert v (getArgStrictness t))
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

        makeThunk :: Bool -> (forall a. Translator a -> Translator a) -> Maybe T.Pattern -> TaggedTExpr -> Translator (Translator Binding, Var)
        makeThunk lock updateContext pat expr = do
            let patternName = pat >>= nameForPattern
            bindVar <- case patternName of
                         Just name -> do
                             prebuilt <- gets (M.lookup (tag expr, P.I name) . (^. builtPatterns))
                             v <- maybe freshName pure prebuilt
                             modify (builtPatterns %~ M.insert (tag expr, P.I name) v)
                             pure v
                         Nothing -> freshName
            modify (strictness %~ M.insert bindVar (getArgStrictness (typeof expr)))
            let name' = fromMaybe ("__thunk_" ++ show (tag expr)) patternName
                binding = do
                    lf <- lockAffineOnPath lock $ updateContext $ convertLambdas expr
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
                  let lambdaForm = Lf NonUpdatable (S.toList fvs) args body
                  modify (builtBindings %~ M.insert (tag lam) lambdaForm)
                  pure (Left lambdaForm)
            where
                collectLambdas' :: Int -> [(Var, T.Pattern, TranslateType, Multiplicity, Tag)] -> TaggedTExpr
                                -> Translator ([(Bool, TypedVar)], LambdaBody)
                collectLambdas' depth toMatch (LambdaT (T.FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
                    varName <- freshName
                    modify (strictness %~ M.insert varName (getArgStrictness from))
                    (vs, expr) <- local (idMap %~ M.insert name ((isRelevant mul, isAffine mul), varName)) $ collectLambdas' (depth + 1) toMatch body
                    pure ((isRelevant mul && not (isFunctionType from), TV varName (typeToTType from)):vs, expr)
                collectLambdas' depth toMatch (LambdaT (T.FunctionType from _ _) mul pat body) = do
                    varName <- freshName
                    modify (strictness %~ M.insert varName (getArgStrictness from))
                    (vs, expr) <- collectLambdas' (depth + 1) ((varName, pat, typeToTType from, mul, tag body):toMatch) body
                    pure ((isRelevant mul && not (isFunctionType from), TV varName (typeToTType from)):vs, expr)
                collectLambdas' depth toMatch expr = do
                    locked <- asks (^. lockAffine)
                    linearBase <- if locked
                                     then pure Nothing
                                     else Just <$> withContext (const True) (const True) (buildCases (reverse toMatch))
                    relevantBase <- Just <$> withContext (const True) (const False) (buildCases (reverse toMatch))
                    affineBase <- if locked
                                     then pure Nothing
                                     else Just <$> withContext (const False) (const True) (buildCases (reverse toMatch))
                    normalBase <- Just <$> withContext (const False) (const False) (buildCases (reverse toMatch))
                    pure ([], LambdaBody linearBase relevantBase affineBase normalBase)
                    where
                        buildCases :: [(Var, T.Pattern, TranslateType, Multiplicity, Tag)] -> Translator CodegenExpr
                        buildCases [] = convert expr
                        buildCases ((v, pat, t, mul, tag):rest) = do
                            rel <- relevantCtx
                            affine <- affineCtx
                            (p, ids) <- convertPattern tag pat
                            local (idMap %~ M.union (M.map (\tv -> ((isRelevant mul, isAffine mul), baseVar tv)) ids)) $ do
                                -- baseExpr <- (if isAffine mul then Free v else id) <$> buildCases rest
                                baseExpr <- buildCases rest
                                pure (Case (Application t (rel && isRelevant mul, affine && isAffine mul) v [])
                                           (NE.singleton (Alt (affine && isAffine mul) p baseExpr)))

        convertLambdas expr = do
            prebuilt <- gets (M.lookup (tag expr) . (^. builtBindings))
            case prebuilt of
              Just (Lf _ caps _ _) -> pure (Right caps)
              Nothing -> do
                  (body, rebound) <- rebindCapturesIn $ do
                      locked <- asks (^. lockAffine)
                      l <- if locked
                              then pure Nothing
                              else Just <$> withContext (const True) (const True) (convert expr)
                      r <- Just <$> withContext (const True) (const False) (convert expr)
                      a <- if locked
                              then pure Nothing
                              else Just <$> withContext (const False) (const True) (convert expr)
                      n <- Just <$> withContext (const False) (const False) (convert expr)
                      pure (LambdaBody l r a n)
                  fvs <- maybe (pure S.empty) (findFVs rebound) (firstBody body)
                  affine <- affineCtx
                  let flag
                          | affine = Updatable
                          | otherwise = Updatable
                      lambdaForm = Lf flag (S.toList fvs) [] body
                  modify (builtBindings %~ M.insert (tag expr) lambdaForm)
                  pure (Left lambdaForm)

        rebindCapturesIn :: Translator a -> Translator (a, S.HashSet Var)
        rebindCapturesIn env = do
            boundIds <- asks (^. idMap)
            rel <- relevantCtx
            let (rebound, vars) = runState (mapM (rebind rel) boundIds) S.empty
            (, vars) <$> local (idMap .~ rebound) env
            where
                rebind :: Bool -> ((Bool, Bool), Var) -> State (S.HashSet Var) ((Bool, Bool), Var)
                rebind True ((True, a), v) = modify (S.insert v) >> pure ((False, a), v)
                rebind _ ((_, a), v) = pure ((False, a), v)

        lookupVar :: P.Identifier -> Translator (Maybe Var)
        lookupVar name = asks ((snd <$>) . M.lookup name . (^. idMap))

        lookupRelevance :: P.Identifier -> Translator Bool
        lookupRelevance name = asks (fst . fst . (M.! name) . (^. idMap))

        lookupAffinity :: P.Identifier -> Translator Bool
        lookupAffinity name = asks (snd . fst . (M.! name) . (^. idMap))

        liftFuncArg :: Bool -> Multiplicity -> TaggedTExpr
                    -> Translator (Atom, Maybe Binding, CodegenExpr -> CodegenExpr)
        liftFuncArg strict mul var@(VariableT t name)
            | not (M.member name (staticContext ^. T.dataConstructors)) = do
                rel <- relevantCtx
                aff <- affineCtx
                argVar <- fromJust <$> lookupVar name
                if strict
                   then do
                       affineVar <- lookupAffinity name
                       matchVar <- freshName
                       -- We can always mark this as false -- the pattern is just a variable
                       let alt = Alt False (VarPattern (TV matchVar (typeToTType t)))
                           matcher = Case (Application (typeToTType t) (True, aff && affineVar) argVar []) . NE.singleton . alt
                       pure (Var matchVar, Nothing, matcher)
                   else do
                       strictVar <- lookupRelevance name
                       if strictVar && rel
                          then do
                              boxVar <- freshName
                              let bind = BoxBinding ("__thunk_" ++ show (tag var)) boxVar argVar
                              pure (Var boxVar, Nothing, Let [bind])
                          else pure (Var argVar, Nothing, id)
        liftFuncArg strict mul arg = do
            let name = "__thunk_" ++ show (tag arg) 
            rel <- relevantCtx
            if strict then do
                cvtArg <- withContext (&& isRelevant mul) (&& isAffine mul) $ convert arg
                matchVar <- freshName
                let alt = Alt False (VarPattern (TV matchVar (typeToTType (typeof arg))))
                    matcher = Case cvtArg . NE.singleton . alt
                pure (Var matchVar, Nothing, matcher)
            else if rel && isRelevant mul then do
                cvtArg <- withContext (&& isRelevant mul) (&& isAffine mul) $ convert arg
                matchVar <- freshName
                bindVar <- freshName
                let alt = Alt False (VarPattern (TV matchVar (typeToTType (typeof arg))))
                    box = BoxBinding name bindVar matchVar
                    matcher = Case cvtArg . NE.singleton . alt . Let [box]
                pure (Var bindVar, Nothing, matcher)
            else do
                cvtArg <- withRelevant (const False) $ convertLambdas arg
                bindVar <- freshName
                let binding = case cvtArg of
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

        lockAffineOnPath :: Bool -> Translator a -> Translator a
        lockAffineOnPath lock = local (lockAffine %~ (|| lock))

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

