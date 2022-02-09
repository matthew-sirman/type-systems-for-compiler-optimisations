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
    , Type(..)
    , Arrow(..)
    , typeof
    )

import qualified Builtin.Codegen as B

import Compiler.Size

import qualified Data.List.NonEmpty as NE
import Data.List (intercalate)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Graph

import Control.Monad.State
import Control.Monad.Reader
import Control.Lens

import GHC.Generics (Generic)
import Data.Hashable (Hashable)

-- TODO: Remove
import Typing.Checker
import Parser.Parser
import Debug.Trace
import qualified Builtin.Builtin

data Var = V
    { varSize :: Int
    , varID :: Integer
    }
    deriving (Eq, Generic)

instance Show Var where
    show (V _ x) = show x

instance Hashable Var

data PrimitiveLiteral
    = IntLiteral Int
    | RealLiteral Double

instance Show PrimitiveLiteral where
    show (IntLiteral i) = show i
    show (RealLiteral r) = show r

data CodegenExpr
    = Let [Binding] CodegenExpr
    | Case CodegenExpr (NE.NonEmpty Alternative)
    | Application Int Var [Var]
    | PrimApp P.Identifier [Var]
    | ConsApp P.Identifier [CodegenExpr]
    | Variable Var
    | Literal PrimitiveLiteral
    | PackedTuple [Var]
    | Projector Int Int Var

instance Show CodegenExpr where
    show (Let bindings body) = "let " ++ intercalate " and " (map show bindings) ++ " in " ++ show body
    show (Case disc branches) = "case " ++ show disc ++ " of " ++ foldMap (('\n' :) . show) branches
    show (Application arity fun args) = "$" ++ show fun ++ "[" ++ show arity
        ++ "] {" ++ intercalate ", " (map (('$':) . show) args) ++ "}"
    show (PrimApp fun args) = show fun ++ " {" ++ intercalate ", " (map (('$':) . show) args) ++ "}"
    show (ConsApp fun args) = show fun ++ " {" ++ intercalate ", " (map show args) ++ "}"
    show (Variable name) = "$" ++ show name
    show (Literal lit) = show lit
    show (PackedTuple vs) = "(" ++ intercalate ", " (map (('$':) . show) vs) ++ ")"
    show (Projector i s v) = "sel-" ++ show i ++ "-" ++ show s ++ " " ++ "$v"

data Binding
    = LazyBinding (Maybe P.Identifier) Var LambdaForm
    | EagerBinding (Maybe P.Identifier) Integer Pattern CodegenExpr

instance Show Binding where
    show (LazyBinding (Just (P.I n)) v lf) = "$" ++ show v ++ "[" ++ n ++ "] = " ++ show lf
    show (LazyBinding Nothing v lf) = "$" ++ show v ++ " = " ++ show lf
    show (EagerBinding (Just (P.I n)) _ p expr) = show p ++ "[" ++ n ++ "] = " ++ show expr
    show (EagerBinding Nothing _ p expr) = show p ++ " = " ++ show expr

data Pattern
    = VarPattern Var
    | ConsPattern P.Identifier [Pattern]
    | LiteralPattern (P.Literal Pattern)

instance Show Pattern where
    show (VarPattern v) = "$" ++ show v
    show (ConsPattern name ps) = "(" ++ show name ++ concatMap ((' ':) . show) ps ++ ")"
    show (LiteralPattern lit) = show lit

data LambdaForm = Lf [Var] (Maybe Int) [(Bool, Var)] CodegenExpr

instance Show LambdaForm where
    show (Lf captures _ args body) = "{" ++ intercalate ", " (map (('$':) . show) captures) ++ "} \\{" 
        ++ intercalate ", " (map (('$':) . show . snd) args) ++ "} -> " ++ show body

data Alternative = Alt Pattern CodegenExpr

instance Show Alternative where
    show (Alt pattern body) = "| " ++ show pattern ++ " -> " ++ show body

type IdMap = M.HashMap P.Identifier Var

data TranslatorContext = TranslatorContext
    { _idMap :: IdMap
    , _bound :: S.HashSet Var
    }

makeLenses ''TranslatorContext

data TranslatorState = TranslatorState
    { _nextVar :: Integer
    , _arityMap :: M.HashMap Var Int
    }

makeLenses ''TranslatorState

type Translator a = ReaderT TranslatorContext (State TranslatorState) a

findFVs :: CodegenExpr -> Translator (S.HashSet Var)
findFVs (Let bindings body) =
    let extractName (LazyBinding _ v _) = S.singleton v
        extractName (EagerBinding _ _ p _) = namesInPattern p
        findBindFVs (LazyBinding _ _ (Lf _ _ binds e)) =
            local (bound %~ S.union (S.fromList (map snd binds))) $ findFVs e
        findBindFVs (EagerBinding _ _ _ e) = findFVs e
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
findFVs (Application _ fun args) = do
    fnFVs <- checkFV fun
    argFVs <- mapM checkFV args
    pure (S.unions (fnFVs:argFVs))
findFVs (PrimApp _ args) = S.unions <$> mapM checkFV args
findFVs (ConsApp _ args) = S.unions <$> mapM findFVs args
findFVs (Variable v) = checkFV v
findFVs (Literal lit) = pure S.empty
findFVs (PackedTuple ts) = S.unions <$> mapM checkFV ts
findFVs (Projector _ _ v) = checkFV v

checkFV :: Var -> Translator (S.HashSet Var)
checkFV v = do
    isBound <- asks (S.member v . (^. bound))
    if isBound
       then pure S.empty
       else pure (S.singleton v)

namesInPattern :: Pattern -> S.HashSet Var
namesInPattern (VarPattern v) = S.singleton v
namesInPattern (ConsPattern _ ps) = S.unions (map namesInPattern ps)
namesInPattern (LiteralPattern lit) = namesInLit lit
    where
        namesInLit :: P.Literal Pattern -> S.HashSet Var
        namesInLit (P.ListLiteral ls) = S.unions (map namesInPattern ls)
        namesInLit (P.TupleLiteral ts) = S.unions (map namesInPattern ts)
        namesInLit _ = S.empty

convertAST :: T.TypedExpr -> T.MultiplicityPoset -> CodegenExpr
convertAST expr poset =
    let initCtx = TranslatorContext
            { _idMap = M.empty
            , _bound = S.empty
            }
        initState = TranslatorState
            { _nextVar = 0
            , _arityMap = M.empty
            }
     in evalState (runReaderT (cvtAST expr) initCtx) initState
    where
        cvtAST :: T.TypedExpr -> Translator CodegenExpr
        cvtAST (T.Let _ bindings body) = do
            newVars <- getAllVars
            let added = M.foldr S.insert S.empty newVars

            local (idMap %~ M.union newVars) $ do
                newBindings <- convertLetBindings bindings
                newBody <- cvtAST body
                graph <- buildOrderGraph added newBindings
                pure (buildLetPath newBody (stronglyConnComp graph))
            where
                getAllVars :: Translator IdMap
                getAllVars = foldM (\vs (p, m) -> addPattern m p vs) M.empty [(p, m) | (T.TypedLetBinding m p _) <- bindings]

                convertLetBindings :: [T.TypedLetBinding] -> Translator [Binding]
                convertLetBindings [] = pure []
                convertLetBindings (T.TypedLetBinding m (T.VariablePattern t name) expr:bs) = do
                    nm <- asks ((M.! name) . (^. idMap))
                    binds <- convertLetBindings bs
                    bind <- local (bound %~ S.insert nm) $
                        if isLambda expr || not (isEager m)
                           then LazyBinding (Just name) nm <$> collectLambdas nm expr
                           else EagerBinding (Just name) <$> nextVarID <*> pure (VarPattern nm) <*> cvtAST expr
                    pure (bind:binds)
                convertLetBindings (T.TypedLetBinding m pattern expr:bs)
                    | isEager m = do
                        pat <- convertPattern pattern
                        expr' <- cvtAST expr
                        binds <- convertLetBindings bs
                        eagerTag <- nextVarID
                        pure (EagerBinding Nothing eagerTag pat expr':binds)
                    | otherwise = do
                        -- Note that we can never pattern match a lambda, so expr cannot
                        -- be a lambda here (though it may still be a lambda form if it is lazy!)
                        pat <- convertPattern pattern
                        let varsInPattern = listVars pat []
                        nm <- freshName pointerSize
                        binds <- convertLetBindings bs
                        case varsInPattern of
                          [] -> pure binds
                          _ -> local (bound %~ S.union (S.fromList varsInPattern)) $ do
                              let packer = PackedTuple varsInPattern
                              (Lf clVars sz fnArgs e) <- collectLambdas nm expr
                              let transform = Case e (NE.singleton (Alt pat packer))
                              let bind = LazyBinding Nothing nm (Lf clVars sz fnArgs transform)
                              let projectors = makeProjectors 0 varsInPattern
                                  makeProjectors :: Int -> [Var] -> [Binding]
                                  makeProjectors _ [] = binds
                                  makeProjectors p (v@(V sz _):rest) = binder : r
                                      where
                                          binder :: Binding
                                          binder = LazyBinding Nothing v lf

                                          lf :: LambdaForm
                                          lf = Lf [nm] (Just sz) [] (Projector p sz nm)

                                          r :: [Binding]
                                          r = makeProjectors (p + sz) rest
                              pure (bind:projectors)

                buildOrderGraph :: S.HashSet Var -> [Binding] -> Translator [(Binding, Integer, [Integer])]
                buildOrderGraph _ [] = pure []
                buildOrderGraph mrecs (bind@(EagerBinding _ tag _ body):bs) = do
                    fvs <- findFVs body
                    let node = (bind, tag, map varID (S.toList (S.intersection mrecs fvs)))
                    (node:) <$> buildOrderGraph mrecs bs
                buildOrderGraph mrecs (bind@(LazyBinding _ v (Lf caps _ _ _)):bs) = do
                    let node = (bind, varID v, [varID n | n <- caps, n `S.member` mrecs])
                    (node:) <$> buildOrderGraph mrecs bs

                buildLetPath :: CodegenExpr -> [SCC Binding] -> CodegenExpr
                buildLetPath base [] = base
                buildLetPath base (AcyclicSCC v:sccs) = Let [v] (buildLetPath base sccs)
                buildLetPath base (CyclicSCC vs:sccs) = Let vs (buildLetPath base sccs)

        cvtAST (T.Case _ mul disc branches) = do
            disc' <- cvtAST disc
            branches' <- mapM convertBranch branches
            pure (Case disc' branches')
            where
                convertBranch :: T.TypedCaseBranch -> Translator Alternative
                convertBranch (T.TypedCaseBranch p expr) = do
                    ids' <- asks (^. idMap) >>= addPattern mul p
                    local (idMap .~ ids') $ do
                        e' <- cvtAST expr
                        p' <- convertPattern p
                        pure (Alt p' e')

        cvtAST (T.Application _ fun arg) = do
            let (FunctionType _ (Arrow mul) _) = typeof fun
            collectArgs fun [(mul, arg)]
            where
                collectArgs :: T.TypedExpr -> [(Multiplicity, T.TypedExpr)] -> Translator CodegenExpr
                collectArgs (T.Application _ f a) args =
                    let (FunctionType _ (Arrow mul) _) = typeof f
                     in collectArgs f ((mul, a):args)
                collectArgs var@(T.Variable _ name) args
                    | M.member name B.functions = liftArgs args (PrimApp name)
                    | M.member name Builtin.Builtin.constructors = ConsApp name <$> mapM (cvtAST . snd) args
                    | otherwise = do
                        funVar <- asks ((M.! name) . (^. idMap))
                        arity <- gets ((M.! funVar) . (^. arityMap))
                        liftArgs args (Application arity funVar)
                collectArgs expr args = do
                    funExpr <- cvtAST expr
                    case funExpr of
                      Let binds (Variable funVar) -> do
                          arity <- gets ((M.! funVar) . (^. arityMap))
                          liftArgs args (Let binds . Application arity funVar)
                      _ -> do
                          funVar <- freshName pointerSize
                          eagerTag <- nextVarID
                          liftArgs args (Let [EagerBinding Nothing eagerTag (VarPattern funVar) funExpr] . Application 0 funVar)

                liftArgs :: [(Multiplicity, T.TypedExpr)] -> ([Var] -> CodegenExpr) -> Translator CodegenExpr
                liftArgs args app = do
                    boundArgs <- forM args $ \(mul, arg) -> do
                        argName <- freshName (if isEager mul then sizeof (typeof arg) else pointerSize)
                        (argName,) <$>
                            if isEager mul
                               then EagerBinding Nothing <$> nextVarID <*> pure (VarPattern argName) <*> cvtAST arg
                               else LazyBinding Nothing argName <$> collectLambdas argName arg
                    let (argVars, binds) = unzip boundArgs
                    pure (Let binds (app argVars))
        cvtAST lam@(T.Lambda {}) = do
            lambdaName <- freshName pointerSize
            bind <- LazyBinding Nothing lambdaName <$> collectLambdas lambdaName lam
            pure (Let [bind] (Variable lambdaName))
        cvtAST (T.Variable t name) = do
            asks (Variable . (M.! name) . (^. idMap))
        cvtAST (T.Literal t val) = do
            convertLit val
            where
                convertLit :: P.Literal T.TypedExpr -> Translator CodegenExpr
                convertLit (P.IntLiteral i) = pure (Literal (IntLiteral i))
                convertLit (P.RealLiteral r) = pure (Literal (RealLiteral r))
                convertLit (P.ListLiteral ls) = do
                    makeList ls
                    where
                        makeList :: [T.TypedExpr] -> Translator CodegenExpr
                        makeList [] = pure (ConsApp (P.I "[]") [])
                        makeList (e:es) = do
                            e' <- cvtAST e
                            es' <- makeList es
                            pure (ConsApp (P.I "::") [e', es'])
                convertLit (P.TupleLiteral ts) = do
                    bindings <- forM ts $ \expr -> do
                        if isLambda expr
                           then do
                               nm <- freshName pointerSize
                               (nm,) . LazyBinding Nothing nm <$> collectLambdas nm expr
                           else do
                               nm <- freshName (sizeof (typeof expr))
                               eagerTag <- nextVarID
                               (nm,) . EagerBinding Nothing eagerTag (VarPattern nm) <$> cvtAST expr
                    let tuple = PackedTuple (map fst bindings)
                    pure (Let (map snd bindings) (PackedTuple (map fst bindings)))

        listVars :: Pattern -> [Var] -> [Var]
        listVars (VarPattern v) vs = v:vs
        listVars (ConsPattern _ ps) vs = foldr listVars vs ps
        listVars (LiteralPattern lit) vs = listLitPattern lit
            where
                listLitPattern :: P.Literal Pattern -> [Var]
                listLitPattern (P.ListLiteral ls) = foldr listVars vs ls
                listLitPattern (P.TupleLiteral ts) = foldr listVars vs ts
                listLitPattern _ = vs 

        collectLambdas :: Var -> T.TypedExpr -> Translator LambdaForm
        collectLambdas bindName lam@(T.Lambda (FunctionType from _ _) mul _ _) = do
            varName <- freshName (if isEager mul then sizeof from else pointerSize)
            (vs, expr) <- case lam of
                            T.Lambda _ _ (T.VariablePattern _ name) body ->
                                local (idMap %~ M.insert name varName) $ collectLambdas' 1 [] body
                            T.Lambda _ mul pattern body -> collectLambdas' 1 [(varName, pattern, mul)] body
            fvs <- local (bound %~ S.insert varName) $ findFVs expr
            pure (Lf (S.toList fvs) Nothing ((isEager mul, varName):vs) expr)
            where
                collectLambdas' :: Int -> [(Var, T.Pattern, Multiplicity)] -> T.TypedExpr
                                -> Translator ([(Bool, Var)], CodegenExpr)
                collectLambdas' depth toMatch (T.Lambda (FunctionType from _ _) mul (T.VariablePattern _ name) body) = do
                    varName <- freshName (if isEager mul then sizeof from else pointerSize)
                    (vs, expr) <- local (idMap %~ M.insert name varName) $ collectLambdas' (depth + 1) toMatch body
                    pure ((isEager mul, varName):vs, expr)
                collectLambdas' depth toMatch (T.Lambda (FunctionType from _ _) mul pattern body) = do
                    varName <- freshName (if isEager mul then sizeof from else pointerSize)
                    (vs, expr) <- collectLambdas' (depth + 1) ((varName, pattern, mul):toMatch) body
                    pure ((isEager mul, varName):vs, expr)
                collectLambdas' depth toMatch expr = do
                    base <- buildCases (reverse toMatch)
                    pure ([], base)
                    where
                        buildCases :: [(Var, T.Pattern, Multiplicity)] -> Translator CodegenExpr
                        buildCases [] = do
                            modify (arityMap %~ M.insert bindName depth)
                            cvtAST expr
                        buildCases ((v, pat, mul):rest) = do
                            ids' <- asks (^. idMap) >>= addPattern mul pat
                            local (idMap .~ ids') $ do
                                baseExpr <- buildCases rest
                                cvtPat <- convertPattern pat
                                pure (Case (Variable v) (NE.singleton (Alt cvtPat baseExpr)))
        collectLambdas bindName expr = do
            modify (arityMap %~ M.insert bindName 0)
            expr' <- cvtAST expr
            fvs <- findFVs expr'
            pure (Lf (S.toList fvs) (Just (sizeof (typeof expr))) [] expr')

        addPattern :: Multiplicity -> T.Pattern -> IdMap -> Translator IdMap
        addPattern mul (T.VariablePattern t name) mp = do
            nm <- freshName (sizeof t)
            pure (M.insert name nm mp)
        addPattern mul (T.ConstructorPattern name ps) mp = foldM (flip (addPattern mul)) mp ps
        addPattern mul (T.LiteralPattern lit) mp = addLitPattern lit
            where
                addLitPattern :: P.Literal T.Pattern -> Translator IdMap
                addLitPattern (P.ListLiteral ls) = foldM (flip (addPattern mul)) mp ls
                addLitPattern (P.TupleLiteral ts) = foldM (flip (addPattern mul)) mp ts
                addLitPattern _ = pure mp

        convertPattern :: T.Pattern -> Translator Pattern
        convertPattern (T.VariablePattern t name) = asks (VarPattern . (M.! name) . (^. idMap))
        convertPattern (T.ConstructorPattern cons ps) = ConsPattern cons <$> mapM convertPattern ps
        convertPattern (T.LiteralPattern lit) = LiteralPattern <$> convertLitPattern lit
            where
                convertLitPattern :: P.Literal T.Pattern -> Translator (P.Literal Pattern)
                convertLitPattern (P.IntLiteral i) = pure (P.IntLiteral i)
                convertLitPattern (P.RealLiteral r) = pure (P.RealLiteral r)
                convertLitPattern (P.ListLiteral ls) = P.ListLiteral <$> mapM convertPattern ls
                convertLitPattern (P.TupleLiteral ts) = P.TupleLiteral <$> mapM convertPattern ts

        isEager :: Multiplicity -> Bool
        isEager mul = P.leq mul (T.MAtom P.Relevant) poset

        isLambda :: T.TypedExpr -> Bool
        isLambda (T.Lambda {}) = True
        isLambda _ = False

        freshName :: Int -> Translator Var
        freshName vsize = do
            V vsize <$> nextVarID

        nextVarID :: Translator Integer
        nextVarID = do
            v <- gets (^. nextVar)
            modify (nextVar %~ (+1))
            pure v

testTranslate :: String -> CodegenExpr
testTranslate s =
    let (Right parsed) = test_parseExpr s
        (Right (typed, poset)) = typecheck Builtin.Builtin.defaultBuiltins parsed
     in convertAST typed poset
