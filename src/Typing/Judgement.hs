{-# LANGUAGE RankNTypes #-}
module Typing.Judgement where

import Parser.AST 
    ( Identifier(..)
    , SourcePattern(..)
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

extendGeneralise, extendNormal :: Context -> [(Multiplicity, Loc SourcePattern, Type)]
                               -> Checker (Context, [Pattern])
extendGeneralise = extend True
extendNormal = extend False

extend :: Bool -> Context -> [(Multiplicity, Loc SourcePattern, Type)] -> Checker (Context, [Pattern])
extend _ ctx [] = pure (ctx, [])
extend generaliseTypes context (patTriple:patTriples) = do
    (ctx', pat) <- extend' context patTriple
    ((pat:) <$>) <$> extend generaliseTypes ctx' patTriples
    where
        extend' :: Context -> (Multiplicity, Loc SourcePattern, Type) -> Checker (Context, Pattern)
        extend' ctx (mul, L loc (VarPattern name), t) = do
            termVar <- createTermFor (L loc name)

            poset <- gets (^. mulRelation)
            when (P.maybeLeq mul Affine poset) $ modify (varFrame . affineVars %~ S.insert termVar)
            when (P.maybeLeq mul Relevant poset) $ modify (varFrame . relevantVars %~ S.insert termVar)
            gen <- generalise ctx t mul
            pure ((termContext %~ M.insert name gen) ctx, VariablePattern (fst gen ^. baseType) name)
        extend' ctx (mul, L loc (ConsPattern name patterns), t) = do
            conss <- asks (^. dataConstructors)
            case M.lookup name conss of
              Nothing -> typeError $ ConstructorNotInScope loc name
              Just scheme -> do
                  consFunc <- instantiate scheme
                  (ConstructorPattern name <$>) <$> checkPatterns ctx consFunc patterns
            where
                checkPatterns :: Context -> Type -> [Loc SourcePattern] -> Checker (Context, [Pattern])
                checkPatterns _ (FunctionType {}) [] = typeError $ IncompletePattern loc name
                checkPatterns ctx retTy [] = do
                    unify loc t retTy
                    pure (ctx, [])
                checkPatterns ctx' (FunctionType from (Arrow argMul) to) (sp:sps) = do
                    (ctx'', ps)  <- checkPatterns ctx' to sps
                    ((:ps) <$>) <$> extend' ctx'' (mul @* argMul, sp, from)
                checkPatterns ctx' t _ = do
                    typeError $ TooManyArguments loc name
        extend' ctx (mul, L loc (LitPattern literal), t) =
            (LiteralPattern <$>) <$> extendLiteral ctx mul loc literal t

        extendLiteral :: Context -> Multiplicity -> SourceLocation -> Literal (Loc SourcePattern) -> Type -> Checker (Context, Literal Pattern)
        extendLiteral ctx _ loc (IntLiteral i) t = do
            unify loc t B.intType
            pure (ctx, IntLiteral i)
        extendLiteral ctx _ loc (RealLiteral r) t = do
            unify loc t B.realType
            pure (ctx, RealLiteral r)
        extendLiteral ctx mul loc (ListLiteral ts) t = do
            listType <- freshPolyType
            unify loc t (TypeApp B.listTypeCon listType)
            (ListLiteral <$>) <$> foldList listType ctx ts
            where
                foldList :: Type -> Context -> [Loc SourcePattern] -> Checker (Context, [Pattern])
                foldList _ elemCtx [] = pure (elemCtx, [])
                foldList listT elemCtx (p:ps) = do
                    (ctx', pat) <- extend' elemCtx (mul, p, listT)
                    ((pat:) <$>) <$> foldList listT ctx' ps
        extendLiteral ctx mul loc (TupleLiteral ts) t = do
            typeToFreshMap <- mapM (\t -> (,) t <$> freshPolyType) ts
            unify loc t (TupleType (map snd typeToFreshMap))
            (TupleLiteral <$>) <$> foldTuple ctx typeToFreshMap
            where
                foldTuple :: Context -> [(Loc SourcePattern, Type)] -> Checker (Context, [Pattern])
                foldTuple elemCtx [] = pure (elemCtx, [])
                foldTuple elemCtx ((pattern, elemType):ps) = do
                    (ctx', pat) <- extend' elemCtx (mul, pattern, elemType)
                    ((pat:) <$>) <$> foldTuple ctx' ps

        generalise :: Context -> Type -> Multiplicity -> Checker (TypeScheme, Multiplicity)
        generalise ctx t mul
            | generaliseTypes = do
                tRep <- typeRepresentative t
                mulRel <- gets (^. mulRelation)
                let freeTVars = S.difference (ftv tRep) (ftv ctx)
                    freeMVars = S.filter ((`P.unlimited` mulRel) . MPoly) $ S.difference (fuv tRep) (fuv ctx)

                freshTVarMap <- M.fromList <$> mapM (\v -> (,) v <$> freshTVar) (S.toList freeTVars)
                freshMVarMap <- M.fromList <$> mapM (\m -> (,) m <$> freshMVar) (S.toList freeMVars)

                let newBase = substitute (M.map Poly freshTVarMap) (M.map MPoly freshMVarMap) tRep

                pure (TypeScheme (S.fromList (M.elems freshTVarMap)) (S.fromList (M.elems freshMVarMap)) newBase, mul)
            | otherwise = pure (TypeScheme S.empty S.empty t, mul)

checkRelevant :: Checker ()
checkRelevant = do
    addedThisFrame <- gets (S.toList . (^. stackFrame . addedTermNames))
    relevant <- gets (^. varFrame . relevantVars)
    remaining <- filterM (isRelevant relevant) addedThisFrame
    unless (null remaining) $ typeError (TypeErrorList $ map createError remaining)
    where
        isRelevant :: VarSet -> Loc Identifier -> Checker Bool
        isRelevant relevant (L _ name) = do
            mappedTermVar <- gets (M.lookup name . (^. stackFrame . termNameContext))
            case mappedTermVar of
              Nothing -> pure False
              Just var -> pure (var `S.member` relevant)

        createError :: Loc Identifier -> TypeError
        createError (L loc name) = RelevancyViolation loc name

typeRepresentative :: Type -> Checker Type
typeRepresentative t@(Poly {}) = do
    rep <- findTypeRep t
    if rep == t
       then pure rep
       else typeRepresentative rep
typeRepresentative t@(Ground {}) = pure t
typeRepresentative (TypeApp con arg) =
    TypeApp <$> typeRepresentative con <*> typeRepresentative arg
typeRepresentative (FunctionType from (Arrow arrow) to) =
    FunctionType <$> typeRepresentative from <*> (Arrow <$> mulRepresentative arrow) <*> typeRepresentative to
typeRepresentative (TupleType ts) =
    TupleType <$> mapM typeRepresentative ts

mulRepresentative :: Multiplicity -> Checker Multiplicity
mulRepresentative m@(MPoly {}) = do
    rep <- findMulRep m
    if rep == m
       then pure rep
       else mulRepresentative rep
mulRepresentative m@(MAtom {}) = pure m
mulRepresentative (MProd lhs rhs) =
    MProd <$> mulRepresentative lhs <*> mulRepresentative rhs

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
            termVar <- gets ((M.! name) . (^. stackFrame . termNameContext))

            mulRel <- gets (^. mulRelation)
            -- If the variable we are trying to use is in the zero set, it cannot be consumed.
            isZeroed <- checkInSet termVar zeroVars
            when isZeroed $ typeError $ AffinityViolation loc name
            -- If the variable is affine constrained, but affine variables cannot be used in the constraint
            -- context, then throw
            isAffine <- checkInSet termVar affineVars
            when (isAffine && not (P.maybeLeq mul Affine mulRel)) $ typeError $ ContextAffinityViolation loc name

            isRelevant <- checkInSet termVar relevantVars

            -- Now we consume the variable, as it has passed the checks
            -- We actually don't logically need to check for the deletions if they are in
            -- the set. However, if we already know they are not, it is more efficient
            -- to just not run the delete function.
            --
            -- Once an affine variable is consumed, it is removed from the affine set, and placed
            -- into the zero set. This indicates that it can no longer be used.
            when isAffine $ modify (varFrame . affineVars %~ S.delete termVar)
            -- When a relevant variable is consumed, then the relevancy constraint has been satisfied
            -- so we can drop the constraint and treat it as a normal variable (unless it was linear,
            -- in which case it will be zeroed)
            -- If, however, the context it was used in was not guaranteed to use the variable (e.g.
            -- calling an affine function with it) then we don't drop the constraint.
            when (isRelevant && P.maybeLeq mul Relevant mulRel) $
                modify (varFrame . relevantVars %~ S.delete termVar)
            -- If we have consumed an affine variable, it can no longer be used, so we emplace it in
            -- the zero set.
            when isAffine $ modify (varFrame . zeroVars %~ S.insert termVar)

        checkInSet :: TermVar -> Lens' CheckVarFrame VarSet -> Checker Bool
        checkInSet termVar set = gets (S.member termVar . (^. varFrame . set))

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

freshTermVar :: Checker TermVar
freshTermVar = do
    (var Stream.:> rest) <- gets (^. freshTermVars)
    modify (freshTermVars .~ rest)
    pure var

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

annotationToType :: Annotated a -> Checker Type
annotationToType (Annotated _ Nothing) = freshPolyType
annotationToType (Annotated _ (Just t)) = createTypeFor (syntax t)

annotationToMultiplicity :: Maybe (Loc MultiplicityExpr) -> Checker Multiplicity
annotationToMultiplicity Nothing = pure (MAtom Normal) -- freshPolyMul
annotationToMultiplicity (Just mul) = createMulFor (syntax mul)

createTermFor :: Loc Identifier -> Checker TermVar
createTermFor name = do
    exists <- gets (S.member name . (^. stackFrame . addedTermNames))
    if exists
       then typeError $ DuplicateVariableDefinition (location name) (syntax name)
       else do
           newTermVar <- freshTermVar
           modify ( (stackFrame . addedTermNames %~ S.insert name)
                  . (stackFrame . termNameContext %~ M.insert (syntax name) newTermVar))
           pure newTermVar

createTypeFor :: TypeExpr -> Checker Type
createTypeFor (TEGround name) = pure (Ground name)
createTypeFor (TEPoly poly) = do
    typeNames <- gets (^. stackFrame . typeNameContext)
    case M.lookup poly typeNames of
      Just v -> pure v
      Nothing -> do
          newTypeVar <- freshTVar
          modify (typeVarAssignments %~ M.insert newTypeVar poly)
          let polyType = Poly newTypeVar
          modify (stackFrame . typeNameContext %~ M.insert poly polyType)
          pure polyType
createTypeFor (TEApp con arg) = do
    conType <- createTypeFor (syntax con)
    argType <- createTypeFor (syntax arg)
    pure (TypeApp conType argType)
createTypeFor (TEArrow from arrow to) = do
    fromType <- createTypeFor (syntax from)
    toType <- createTypeFor (syntax to)
    arrowType <- createArrowFor (syntax arrow)
    pure (FunctionType fromType arrowType toType)
createTypeFor TEUnit = pure B.unitType
createTypeFor (TETuple ts) = do
    tupleTypes <- mapM (createTypeFor . syntax) ts
    pure (TupleType tupleTypes)
createTypeFor (TEList t) = TypeApp B.listTypeCon <$> createTypeFor (syntax t)

createArrowFor :: ArrowExpr -> Checker Arrow
createArrowFor (ArrowExpr Nothing) = typeError $ GenericError Nothing "SHOULD NEVER HAPPEN! Unannotated arrow."
createArrowFor (ArrowExpr (Just m)) = do
    Arrow <$> createMulFor (syntax m)

createMulFor :: MultiplicityExpr -> Checker Multiplicity
createMulFor (MEPoly poly) = do
    mulNames <- gets (^. stackFrame . mulNameContext)
    case M.lookup poly mulNames of
      Just v -> pure v
      Nothing -> do
          newMulVar <- freshMVar
          modify (mulVarAssignments %~ M.insert newMulVar poly)
          let polyMul = MPoly newMulVar
          modify (stackFrame . mulNameContext %~ M.insert poly polyMul)
          pure polyMul
createMulFor (MEAtom atom) = pure (MAtom atom)
createMulFor (MEProd lhs rhs) = MProd <$> createMulFor lhs <*> createMulFor rhs

unify :: SourceLocation -> Type -> Type -> Checker ()
unify loc ta tb = do
    ra <- findTypeRep ta
    rb <- findTypeRep tb
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
            unify loc con con'
            unify loc arg arg'
        unify' (FunctionType from (Arrow arrow) to) (FunctionType from' (Arrow arrow') to') = do
            unify loc from from'
            mulUnify loc arrow arrow'
            unify loc to to'
        unify' (TupleType ts) (TupleType ts') = zipWithM_ (flip (unify loc)) ts ts'
        unify' t t' = typeError $ UnificationFailure loc t t'

mulUnify :: SourceLocation -> Multiplicity -> Multiplicity -> Checker ()
mulUnify loc ma mb = do
    ra <- findMulRep ma
    rb <- findMulRep mb
    unify' ra rb
    where
        unify' :: Multiplicity -> Multiplicity -> Checker ()
        unify' (MAtom a) (MAtom b)
            | a == b = pure ()
            | otherwise = typeError $ MAtomUnificationFailure loc a b
        unify' (MProd l r) (MProd l' r') = do
            unify' l l'
            unify' r r'
        unify' p q = do
            addRelation loc p q
            addRelation loc q p
            modify (mulEquivalences %~ DS.union p q)

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
bindTypeVar _ var (Poly var')
    | var == var' = pure ()
bindTypeVar loc var t
    | var `S.member` ftv t = typeError $ OccursCheckFailure loc var t
    | otherwise = modify (typeEquivalences %~ DS.union (Poly var) t)

findTypeRep :: Type -> Checker Type
findTypeRep t = do
    equivRel <- gets (^. typeEquivalences)
    pure (maximum $ DS.equivalences t equivRel)

findMulRep :: Multiplicity  -> Checker Multiplicity
findMulRep m = do
    equivRel <- gets (^. mulEquivalences)
    pure (maximum $ DS.equivalences m equivRel)

checkTypeEntails :: Context -> Type -> Maybe (Loc TypeExpr) -> Checker ()
checkTypeEntails _ _ Nothing = pure ()
checkTypeEntails ctx inferredType (Just ann) = do
    itr <- findTypeRep inferredType
    evalStateT (entails itr ann) M.empty
    where
        ctxFtvs :: S.HashSet TypeVar
        ctxFtvs = ftv ctx

        entails :: Type -> Loc TypeExpr
                -> StateT (M.HashMap TypeVar Type) (ExceptT (TypeError, TypeVarMap) CheckerState) ()
        entails t@(Poly p) expr = do
            exprType <- lift $ createTypeFor (syntax expr)
            subType <- gets (M.lookup p)
            case subType of
              Just t
                | t /= exprType -> lift $ typeError $ EntailmentMultiAssign (location expr) p
              _ -> do
                  lift $ bindTypeVar (location expr) p exprType
                  modify (M.insert p exprType)
        entails t@(Ground name) (L loc (TEGround name'))
            | name == name' = pure ()
            | otherwise = lift $ typeError $ EntailmentFailure loc t
        entails (TypeApp con arg) (L _ (TEApp con' arg')) = do
            entails con con'
            entails arg arg'
        entails t@(TypeApp listCon listArg) (L loc (TEList list))
            | listCon == B.listTypeCon = entails listArg list
            | otherwise = lift $ typeError $ EntailmentFailure loc t
        entails t@(FunctionType from (Arrow mul) to) (L loc (TEArrow from' (L _ (ArrowExpr (Just mul'))) to')) = do
            entails from from'
            lift $ mulEntails mul mul'
            entails to to'
        entails (TupleType ts) (L _ (TETuple ts')) = zipWithM_ entails ts ts'
        entails t (L loc _) = lift $ typeError $ EntailmentFailure loc t

        mulEntails :: Multiplicity -> Loc MultiplicityExpr -> Checker ()
        mulEntails (MAtom inf) (L loc (MEAtom ann))
            | inf P.<=? ann = pure ()
            | otherwise = typeError $ MOrderingViolation loc (MAtom inf) (MAtom ann)
        mulEntails l@(MAtom _) (L loc rm) = do
            r <- createMulFor rm
            typeError $ MOrderingViolation loc l r
        mulEntails p (L loc m) = do
            mul <- createMulFor m
            addRelation loc p mul
            addRelation loc mul p

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

