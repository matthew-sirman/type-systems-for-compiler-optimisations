module Typing.Judgement where

import Parser.AST 
    ( Identifier(..)
    , Pattern(..)
    , ArrowExpr(..)
    , MultiplicityExpr(..)
    , MultiplicityAtom(..)
    , TypeExpr(..)
    , Literal(..)
    , SourceLocation
    , Loc(..)
    , Annotated(..)
    )

import Typing.Types
import qualified Builtin.Types as B

import qualified Util.Stream as Stream
import qualified Util.BoundedPoset as P

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Context)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.DisjointSet as DS
import Data.Maybe (isJust, fromMaybe)

-- TODO: REMOVE
import Debug.Trace

extendGeneralise, extendNormal :: Context -> [(Multiplicity, Loc Pattern, Type)] -> Checker (Context, Checker ())
extendGeneralise = extend True
extendNormal = extend False

extend :: Bool -> Context -> [(Multiplicity, Loc Pattern, Type)] -> Checker (Context, Checker ())
extend generaliseTypes context extensions = do
    relevantSet <- lift $ gets (^. relevantVars)
    ctx' <- foldM extend' context extensions
    pure (ctx', createRelevantChecker relevantSet)
    where
        extend' :: Context -> (Multiplicity, Loc Pattern, Type) -> Checker Context
        extend' ctx (mul, L _ (VarPattern name), t) = do
            poset <- gets (^. mulRelation)
            when (P.maybeLeq mul Affine poset) $ modify (affineVars %~ S.insert name)
            when (P.maybeLeq mul Relevant poset) $ modify (relevantVars %~ S.insert name)
            gen <- generalise ctx t mul
            pure $ (termContext %~ M.insert name gen) ctx
        extend' ctx (mul, L loc (ConsPattern name patterns), t) = do
            conss <- asks (^. dataConstructors)
            case M.lookup name conss of
              Nothing -> typeError $ ConstructorNotInScope loc name
              Just scheme -> do
                  consFunc <- instantiate scheme
                  checkPatterns ctx consFunc patterns
            where
                checkPatterns :: Context -> Type -> [Loc Pattern] -> Checker Context
                checkPatterns _ (FunctionType {}) [] = typeError $ IncompletePattern loc name
                checkPatterns ctx retTy [] = do
                    unify loc t LessThan retTy
                    pure ctx
                checkPatterns ctx' (FunctionType from (Arrow argMul) to) (p:ps) = do
                    ctx'' <- extend' ctx' (mul @* argMul, p, from)
                    checkPatterns ctx'' to ps
                checkPatterns ctx' t _ = do
                    typeError $ TooManyArguments loc name
        extend' ctx (mul, L loc (LitPattern literal), t) = extendLiteral ctx mul loc literal t

        extendLiteral :: Context -> Multiplicity -> SourceLocation -> Literal (Loc Pattern) -> Type -> Checker Context
        extendLiteral ctx _ loc (IntLiteral _) t = do
            unify loc t LessThan B.intType
            pure ctx
        extendLiteral ctx _ loc (RealLiteral _) t = do
            unify loc t LessThan B.realType
            pure ctx
        extendLiteral ctx mul loc (ListLiteral ts) t = do
            listType <- freshPolyType
            unify loc t Equivalent (TypeApp B.listTypeCon listType)
            foldM (combinator listType) ctx ts
            where
                combinator :: Type -> Context -> Loc Pattern -> Checker Context
                combinator listT elemCtx pattern = extend' elemCtx (mul, pattern, listT)
        extendLiteral ctx mul loc (TupleLiteral ts) t = do
            typeToFreshMap <- mapM (\t -> (,) t <$> freshPolyType) ts
            unify loc t Equivalent (TupleType (map snd typeToFreshMap))
            foldM combinator ctx typeToFreshMap
            where
                combinator :: Context -> (Loc Pattern, Type) -> Checker Context
                combinator elemCtx (pattern, elemType) = extend' elemCtx (mul, pattern, elemType)

        createRelevantChecker :: VarSet -> Checker ()
        createRelevantChecker before = do
            after <- lift $ gets (^. relevantVars)
            let remaining = after `S.difference` before
            unless (S.null remaining) $ typeError $ TypeErrorList (violations remaining extensions)
            where
                violations :: VarSet -> [(Multiplicity, Loc Pattern, Type)] -> [TypeError]
                violations remaining = violations'
                    where
                        violations' :: [(Multiplicity, Loc Pattern, Type)] -> [TypeError]
                        violations' [] = []
                        violations' ((_, pattern, _):es) = findViolation pattern <> violations' es

                        findViolation :: Loc Pattern -> [TypeError]
                        findViolation (L loc (VarPattern name))
                            | name `S.member` remaining = [RelevancyViolation loc name]
                            | otherwise = []
                        findViolation (L _ (ConsPattern _ args)) = concatMap findViolation args
                        findViolation (L _ (LitPattern lit)) = findLitViolation lit

                        findLitViolation :: Literal (Loc Pattern) -> [TypeError]
                        findLitViolation (ListLiteral ls) = concatMap findViolation ls
                        findLitViolation (TupleLiteral ts) = concatMap findViolation ts
                        findLitViolation _ = []

        generalise :: Context -> Type -> Multiplicity -> Checker (TypeScheme, Multiplicity)
        generalise ctx t mul
            | generaliseTypes = do
                tRep <- typeRepresentative t
                let freeTVars = S.difference (ftv tRep) (ftv ctx)
                    freeMVars = S.difference (fuv tRep) (fuv ctx)

                trace ("Type: " ++ show tRep ++ ", " ++ show (fuv tRep) ++ ", " ++ show (fuv ctx)) $ pure ()

                freshTVarMap <- M.fromList <$> mapM (\v -> (,) v <$> freshTVar) (S.toList freeTVars)
                freshMVarMap <- M.fromList <$> mapM (\m -> (,) m <$> freshMVar) (S.toList freeMVars)

                let newBase = substitute (M.map Poly freshTVarMap) (M.map MPoly freshMVarMap) tRep

                pure (TypeScheme (M.keysSet freshTVarMap) (M.keysSet freshMVarMap) newBase, mul)
            | otherwise = pure (TypeScheme S.empty S.empty t, mul)

typeRepresentative :: Type -> Checker Type
typeRepresentative t@(Poly {}) = do
    rep <- findRepresentative t
    if rep == t
       then pure rep
       else typeRepresentative rep
typeRepresentative t@(Ground {}) = pure t
typeRepresentative (TypeApp con arg) =
    TypeApp <$> typeRepresentative con <*> typeRepresentative arg
typeRepresentative (FunctionType from arrow to) =
    FunctionType <$> typeRepresentative from <*> pure arrow <*> typeRepresentative to
typeRepresentative (TupleType ts) =
    TupleType <$> mapM typeRepresentative ts

-- mulRepresentative :: Multiplicity -> Checker Multiplicity
-- mulRepresentative m@(MPoly {}) = do
--     rep <- findMulRepresentative m
--     if rep == m
--        then pure rep
--        else mulRepresentative rep
-- mulRepresentative m@(MAtom {}) = pure m
-- mulRepresentative (MProd lhs rhs) =
--     MProd <$> mulRepresentative lhs <*> mulRepresentative rhs

tighten :: Context -> Multiplicity -> Context
tighten ctx constraint = (termContext %~ M.map tightenElem) ctx
    where
        tightenElem :: (TypeScheme, Multiplicity) -> (TypeScheme, Multiplicity)
        tightenElem (scheme, vConstraint) = (scheme, vConstraint @* constraint)

contextLookup :: Context -> SourceLocation -> Identifier -> Checker Type
contextLookup ctx loc name = do
    staticResult <- checkStaticContext
    case staticResult of
      Just t -> pure t
      Nothing ->
        case M.lookup name (ctx ^. termContext) of
          Nothing -> typeError $ VariableNotInScope loc name
          Just (scheme, constraint) -> do
              checkAndConsume constraint
              instantiate scheme
    where
        checkStaticContext :: Checker (Maybe Type)
        checkStaticContext = do
            funcs <- asks (^. defaultFunctions)
            conss <- asks (^. dataConstructors)
            case M.lookup name funcs of
              Just ts -> Just <$> instantiate ts
              Nothing ->
                  case M.lookup name conss of
                    Just ts -> Just <$> instantiate ts
                    Nothing -> pure Nothing

        checkAndConsume :: Multiplicity -> Checker ()
        checkAndConsume mul = do
            mulRel <- gets (^. mulRelation)
            -- If the variable we are trying to use is in the zero set, it cannot be consumed.
            isZeroed <- checkInSet zeroVars
            when isZeroed $ typeError $ AffinityViolation loc name
            -- If the variable is affine constrained, but affine variables cannot be used in the constraint
            -- context, then throw
            isAffine <- checkInSet affineVars
            when (isAffine && not (P.maybeLeq mul Affine mulRel)) $ typeError $ ContextAffinityViolation loc name
            -- If the variable is relevant, but relevant variables cannot be used, then throw
            isRelevant <- checkInSet relevantVars
            when (isRelevant && not (P.maybeLeq mul Relevant mulRel)) $ typeError $ ContextRelevancyViolation loc name

            -- Now we consume the variable, as it has passed the checks
            -- We actually don't logically need to check for the deletions if they are in
            -- the set. However, if we already know they are not, it is more efficient
            -- to just not run the delete function.
            --
            -- Once an affine variable is consumed, it is removed from the affine set, and placed
            -- into the zero set. This indicates that it can no longer be used.
            when isAffine $ modify (affineVars %~ S.delete name)
            -- When a relevant variable is consumed, then the relevancy constraint has been satisfied
            -- so we can drop the constraint and treat it as a normal variable (unless it was linear,
            -- in which case it will be zeroed)
            when isRelevant $ modify (relevantVars %~ S.delete name)
            -- If we have consumed an affine variable, it can no longer be used, so we emplace it in
            -- the zero set.
            when isAffine $ modify (zeroVars %~ S.insert name)

        checkInSet set = S.member name <$> lift (gets (^. set))

instantiate :: TypeScheme -> Checker Type
instantiate scheme = do
    freshTVarMap <- M.fromList <$> mapM (\v -> (,) v <$> freshPolyType) (S.toList $ scheme ^. quantifiedTVars)
    freshMVarMap <- M.fromList <$> mapM (\m -> (,) m <$> freshPolyMul) (S.toList $ scheme ^. quantifiedMVars)

    pure $ substitute freshTVarMap freshMVarMap (scheme ^. baseType)

substitute :: M.HashMap TypeVar Type -> M.HashMap MultiplicityVar Multiplicity -> Type -> Type
substitute tVarMap mVarMap = sub
    where
        sub :: Type -> Type
        sub t@(Poly p) = fromMaybe t (M.lookup p tVarMap)
        sub t@(Ground _) = t
        sub (TypeApp con arg) = TypeApp (sub con) (sub arg)
        sub (FunctionType from (Arrow m) to) = FunctionType (sub from) (Arrow (msub m)) (sub to)
        sub (TupleType ts) = TupleType (map sub ts)

        msub :: Multiplicity -> Multiplicity
        msub m@(MPoly p) = fromMaybe m (M.lookup p mVarMap)
        msub m@(MAtom _) = m
        msub (MProd lhs rhs) = MProd (msub lhs) (msub rhs)

freshTVar :: Checker TypeVar
freshTVar = do
    (var Stream.:> rest) <- gets (^. freshTypeVars)
    modify (freshTypeVars .~ rest)
    pure var

freshPolyType :: Checker Type
freshPolyType = Poly <$> freshTVar

freshMVar :: Checker MultiplicityVar
freshMVar = do
    (var Stream.:> rest) <- gets (^. freshMulVars)
    modify (freshMulVars .~ rest)
    pure var

freshPolyMul :: Checker Multiplicity
freshPolyMul = MPoly <$> freshMVar

-- TODO: Add scoped type variables

annotationToType :: Context -> Annotated a -> Checker (Type, Context)
annotationToType ctx ann = runStateT (annotationToType' ann) ctx

annotationsToTypes :: Traversable t => Context -> t (Annotated a) -> Checker (t Type, Context)
annotationsToTypes ctx anns = runStateT (mapM annotationToType' anns) ctx

annotationToType' :: Annotated a -> StateT Context (ExceptT (TypeError, TypeVarMap) CheckerState) Type
annotationToType' (Annotated _ Nothing) = lift freshPolyType
annotationToType' (Annotated _ (Just t)) = createTypeFor' (syntax t)

annotationToMultiplicity :: Context -> Maybe (Loc MultiplicityExpr) -> Checker (Multiplicity, Context)
annotationToMultiplicity ctx Nothing = (,) <$> freshPolyMul <*> pure ctx
annotationToMultiplicity ctx (Just mul) = createMulFor ctx (syntax mul)

createTypeFor :: Context -> TypeExpr -> Checker (Type, Context)
createTypeFor ctx typeExpr = runStateT (createTypeFor' typeExpr) ctx

createTypeFor' :: TypeExpr -> StateT Context (ExceptT (TypeError, TypeVarMap) CheckerState) Type
createTypeFor' (TEGround name) = pure (Ground name)
createTypeFor' (TEPoly poly) = do
    ctx <- get
    case M.lookup poly (ctx ^. typeNameContext) of
      Just v -> pure v
      Nothing -> do
          newTypeVar <- lift freshTVar
          lift $ modify (varAssignments %~ M.insert newTypeVar poly)
          let polyType = Poly newTypeVar
          modify (typeNameContext %~ M.insert poly polyType)
          pure polyType
createTypeFor' (TEApp con arg) = do
    conType <- createTypeFor' (syntax con)
    argType <- createTypeFor' (syntax arg)
    pure (TypeApp conType argType)
createTypeFor' (TEArrow from arrow to) = do
    fromType <- createTypeFor' (syntax from)
    toType <- createTypeFor' (syntax to)
    ctx <- get
    (arrowType, ctx') <- lift $ createArrowFor ctx (syntax arrow)
    put ctx'
    pure (FunctionType fromType arrowType toType)
createTypeFor' TEUnit = pure B.unitType
createTypeFor' (TETuple ts) = do
    tupleTypes <- mapM (createTypeFor' . syntax) ts
    pure (TupleType tupleTypes)
createTypeFor' (TEList t) = TypeApp B.listTypeCon <$> createTypeFor' (syntax t)

createArrowFor :: Context -> ArrowExpr -> Checker (Arrow, Context)
createArrowFor ctx (ArrowExpr Nothing) = typeError $ GenericError Nothing "SHOULD NEVER HAPPEN! Unannotated arrow." -- do
    -- mvar <- freshPolyMul
    -- pure (Arrow mvar, ctx)
createArrowFor ctx (ArrowExpr (Just m)) = do
    (mul, ctx') <- createMulFor ctx (syntax m)
    pure (Arrow mul, ctx')

createMulFor :: Context -> MultiplicityExpr -> Checker (Multiplicity, Context)
createMulFor ctx mulExpr = runStateT (createMulFor' mulExpr) ctx

createMulFor' :: MultiplicityExpr -> StateT Context (ExceptT (TypeError, TypeVarMap) CheckerState) Multiplicity
createMulFor' (MEPoly poly) = do
    ctx <- get
    case M.lookup poly (ctx ^. mulNameContext) of
      Just v -> pure v
      Nothing -> do
          polyType <- lift freshPolyMul
          modify (mulNameContext %~ M.insert poly polyType)
          pure polyType
createMulFor' (MEAtom atom) = pure (MAtom atom)
createMulFor' (MEProd lhs rhs) = MProd <$> createMulFor' lhs <*> createMulFor' rhs

data MulUnifyType
    = LessThan
    | Equivalent
    deriving (Eq)

unify :: SourceLocation -> Type -> MulUnifyType -> Type -> Checker ()
unify loc ta m tb = do
    ra <- findRepresentative ta
    rb <- findRepresentative tb
    unify' ra rb
    where
        unify' :: Type -> Type -> Checker ()
        unify' p@(Poly {}) q@(Poly {}) = modify (typeEquivalences %~ DS.union p q)
        unify' (Poly p) t = bindTypeVar loc p t
        unify' t (Poly p) = bindTypeVar loc p t
        unify' (Ground g) (Ground g')
            | g == g' = pure ()
            | otherwise = typeError $ GroundUnificationFailure loc g g'
        unify' (TypeApp con arg) (TypeApp con' arg') = do
            unify loc con m con'
            unify loc arg m arg'
        unify' (FunctionType from (Arrow arrow) to) (FunctionType from' (Arrow arrow') to') = do
            unify loc from m from'
            mulUnify loc arrow m arrow'
            unify loc to m to'
        unify' (TupleType ts) (TupleType ts') = zipWithM_ (flip (unify loc) m) ts ts'
        unify' t t' = typeError $ UnificationFailure loc t t'

mulUnify :: SourceLocation -> Multiplicity -> MulUnifyType -> Multiplicity -> Checker ()
mulUnify loc (MAtom a) mode (MAtom b)
    | a == b = pure ()
    | otherwise = typeError $ MAtomUnificationFailure loc a b
mulUnify loc (MProd l r) mode (MProd l' r') = do
    mulUnify loc l mode l'
    mulUnify loc r mode r'
mulUnify loc p mode q
    | mode == LessThan = do
        addRelation loc p q
    | mode == Equivalent = do
        addRelation loc p q
        addRelation loc q p

addRelation :: SourceLocation -> Multiplicity -> Multiplicity -> Checker ()
addRelation loc p' q' = do
    rel <- gets (^. mulRelation)
    case P.addLeq p' q' rel of
      Just rel' -> modify (mulRelation .~ rel')
      Nothing -> typeError $ MOrderingViolation loc p' q'

-- mulUnify loc 
-- 
--         mUnify' :: Multiplicity -> Multiplicity -> Checker ()
--         mUnify' p@(MPoly {}) t = modify (mulEquivalences %~ DS.union p t)
--         mUnify' t p@(MPoly {}) = modify (mulEquivalences %~ DS.union p t)
--         mUnify' (MAtom a) (MAtom b)
--             | a == b = pure ()
--             | otherwise = typeError $ MAtomUnificationFailure loc a b
--         mUnify' (MProd l r) (MProd l' r') = do
--             mUnify' l l'
--             mUnify' r r'
--         -- TODO: Think some more about this particular constraint
--         mUnify' p q = modify (mulEquivalences %~ DS.union p q)

bindTypeVar :: SourceLocation -> TypeVar -> Type -> Checker ()
bindTypeVar loc var t
    | var `S.member` ftv t = typeError $ OccursCheckFailure loc var t
    | otherwise = modify (typeEquivalences %~ DS.union (Poly var) t)

findRepresentative :: Type -> Checker Type
findRepresentative t = do
    equivRel <- gets (^. typeEquivalences)
    pure (maximum $ DS.equivalences t equivRel)

-- findMulRepresentative :: Multiplicity  -> Checker Multiplicity
-- findMulRepresentative m = do
--     equivRel <- gets (^. mulEquivalences)
--     pure (maximum $ DS.equivalences m equivRel)

checkTypeEntails :: Context -> Type -> Maybe (Loc TypeExpr) -> Checker ()
checkTypeEntails _ _ Nothing = pure ()
checkTypeEntails ctx inferredType (Just ann) = do
    itr <- findRepresentative inferredType
    entails itr ann
    where
        ctxFtvs :: S.HashSet TypeVar
        ctxFtvs = ftv ctx

        entails :: Type -> Loc TypeExpr -> Checker ()
        entails t@(Poly p) expr
            | p `S.member` ctxFtvs = typeError $ EntailmentFailure (location expr) t
            | otherwise = do
                exprType <- reconstruct (syntax expr)
                bindTypeVar (location expr) p exprType
        entails t@(Ground name) (L loc (TEGround name'))
            | name == name' = pure ()
            | otherwise = typeError $ EntailmentFailure loc t
        entails (TypeApp con arg) (L _ (TEApp con' arg')) = do
            entails con con'
            entails arg arg'
        entails t@(TypeApp listCon listArg) (L loc (TEList list))
            | listCon == B.listTypeCon = entails listArg list
            | otherwise = typeError $ EntailmentFailure loc t
        entails t@(FunctionType from (Arrow mul) to) (L loc (TEArrow from' (L _ (ArrowExpr (Just mul'))) to')) = do
            entails from from'
            mulEntails mul mul'
            entails to to'
        entails (TupleType ts) (L _ (TETuple ts')) = zipWithM_ entails ts ts'
        entails t (L loc _) = typeError $ EntailmentFailure loc t

        mulEntails :: Multiplicity -> Loc MultiplicityExpr -> Checker ()
        mulEntails (MAtom inf) (L loc (MEAtom ann))
            | inf P.<=? ann = pure ()
            | otherwise = typeError $ MOrderingViolation loc (MAtom inf) (MAtom ann)
        mulEntails l@(MAtom _) (L loc rm) = do
            r <- reconstructMul rm
            typeError $ MOrderingViolation loc l r
        mulEntails p (L loc m) = do
            mul <- reconstructMul m
            addRelation loc p mul
            addRelation loc mul p

        reconstruct :: TypeExpr -> Checker Type
        reconstruct (TEGround name) = pure (Ground name)
        reconstruct (TEPoly p) =
            case M.lookup p (ctx ^. typeNameContext) of
              Just t -> pure t
              Nothing -> typeError $ GenericError (Just $ location ann) "SHOULD NEVER HAPPEN! Type reconstruction failed."
        reconstruct (TEApp con arg) = TypeApp <$> reconstruct (syntax con) <*> reconstruct (syntax arg)
        reconstruct (TEArrow from arrow to) =
            FunctionType <$> reconstruct (syntax from) <*> reconstructArrow (syntax arrow) <*> reconstruct (syntax to)
        reconstruct TEUnit = pure B.unitType
        reconstruct (TETuple ts) = TupleType <$> mapM (reconstruct . syntax) ts
        reconstruct (TEList t) = TypeApp B.listTypeCon <$> reconstruct (syntax t)

        reconstructArrow :: ArrowExpr -> Checker Arrow
        reconstructArrow (ArrowExpr Nothing) = typeError $ GenericError (Just $ location ann) "SHOULD NEVER HAPPEN! Unannotated arrow."
        reconstructArrow (ArrowExpr (Just m)) = Arrow <$> reconstructMul (syntax m)

        reconstructMul :: MultiplicityExpr -> Checker Multiplicity
        reconstructMul (MEPoly p) =
            case M.lookup p (ctx ^. mulNameContext) of
              Just m -> pure m
              Nothing -> typeError $ GenericError (Just $ location ann) "SHOULD NEVER HAPPEN! Multiplicity reconstruction failed."
        reconstructMul (MEAtom atom) = pure (MAtom atom)
        reconstructMul (MEProd lhs rhs) = MProd <$> reconstructMul lhs <*> reconstructMul rhs

infixl 7 @*
(@*) :: Multiplicity -> Multiplicity -> Multiplicity
(MAtom Linear) @* rhs = rhs
lhs @* (MAtom Linear) = lhs
lhs@(MAtom Normal) @* _ = lhs
_ @* rhs@(MAtom Normal) = rhs
(MAtom Affine) @* (MAtom Affine) = MAtom Affine
(MAtom Relevant) @* (MAtom Relevant) = MAtom Relevant
(MAtom Affine) @* (MAtom Relevant) = MAtom Normal
(MAtom Relevant) @* (MAtom Affine) = MAtom Normal
lhs @* rhs = MProd lhs rhs

