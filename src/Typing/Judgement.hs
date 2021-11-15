module Typing.Judgement where

import Parser.AST 
    ( Identifier(..)
    , Pattern(..)
    , ArrowExpr(..)
    , Multiplicity(..)
    , MultiplicityAtom(..)
    , TypeExpr(..)
    , Literal(..)
    , SourceLocation
    , Loc(..)
    , Annotated(..)
    )

import Typing.Types

import qualified Util.Stream as Stream

import Control.Monad.Except
import Control.Monad.State
import Control.Lens hiding (Context)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Maybe (isJust)

extendGeneralise, extendNormal :: Context -> [(MConstraint, Loc Pattern, Type)] -> Checker (Context, SubMap, Checker ())
extendGeneralise = extend True
extendNormal = extend False

extend :: Bool -> Context -> [(MConstraint, Loc Pattern, Type)] -> Checker (Context, SubMap, Checker ())
extend generaliseTypes context extensions = do
    relevantSet <- lift $ gets (^. relevantVars)
    (ctx, sub) <- foldM combinator (context, emptySub) extensions
    pure (ctx, sub, createRelevantChecker relevantSet)
    where
        combinator :: (Context, SubMap) -> (MConstraint, Loc Pattern, Type) -> Checker (Context, SubMap)
        combinator (ctx, sub) (mul, pattern, typeExpr) = do
            (ctx', sub') <- extend' ctx mul pattern typeExpr
            pure (ctx', sub' +. sub)

        extend' :: Context -> MConstraint -> Loc Pattern -> Type -> Checker (Context, SubMap)
        extend' ctx mul@(MConstraint affine relevant) (L _ (VarPattern name)) t = do
            when affine $ modify (affineVars %~ S.insert name)
            when relevant $ modify (relevantVars %~ S.insert name)
            let ctx' = (termContext %~ M.insert name (generalise ctx t, mul)) ctx
            pure (ctx', emptySub)
        extend' ctx mul (L loc (ConsPattern name patterns)) t = undefined
        extend' ctx mul (L loc (LitPattern literal)) t = extendLiteral ctx mul loc literal t

        extendLiteral :: Context -> MConstraint -> SourceLocation -> Literal (Loc Pattern) -> Type -> Checker (Context, SubMap)
        extendLiteral ctx _ loc (IntLiteral _) t = do
            s <- mgu loc t intType
            pure (ctx, s)
        extendLiteral ctx _ loc (RealLiteral _) t = do
            s <- mgu loc t realType
            pure (ctx, s)
        extendLiteral ctx mul loc (ListLiteral ts) t = do
            listType <- freshVarType
            listSub <- mgu loc t (TypeApp listTypeCon listType)
            (ctx', _, s) <- foldM combinator (ctx, substitute listSub listType, listSub) ts
            pure (ctx', s)
            where
                combinator :: (Context, Type, SubMap) -> Loc Pattern -> Checker (Context, Type, SubMap)
                combinator (elemCtx, listT, sub) pattern = do
                    (elemCtx', s) <- extend' elemCtx mul pattern listT
                    pure (elemCtx', substitute s listT, s +. sub)
        extendLiteral ctx mul loc (TupleLiteral ts) t = do
            (ctx', types, s) <- foldM combinator (ctx, [], emptySub) ts
            tupleSub <- mgu loc t (TupleType (reverse types))
            pure (ctx', tupleSub +. s)
            where
                combinator :: (Context, [Type], SubMap) -> Loc Pattern -> Checker (Context, [Type], SubMap)
                combinator (elemCtx, types, sub) pattern = do
                    elemType <- freshVarType
                    (elemCtx', s) <- extend' elemCtx mul pattern elemType
                    pure (elemCtx', substitute s elemType : types, s +. sub)

        createRelevantChecker :: VarSet -> Checker ()
        createRelevantChecker before = do
            after <- lift $ gets (^. relevantVars)
            let remaining = after `S.difference` before
            unless (S.null remaining) $ typeError $ TypeErrorList (violations remaining extensions)
            where
                violations :: VarSet -> [(MConstraint, Loc Pattern, Type)] -> [TypeError]
                violations remaining = violations'
                    where
                        violations' :: [(MConstraint, Loc Pattern, Type)] -> [TypeError]
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

        generalise :: Context -> Type -> TypeScheme
        generalise ctx t 
            | generaliseTypes = TypeScheme (S.toList (S.difference (ftv t) (ftv ctx))) t
            | otherwise = TypeScheme [] t

tighten :: Context -> MConstraint -> Context
tighten ctx constraint = (termContext %~ M.map tightenElem) ctx
    where
        tightenElem :: (TypeScheme, MConstraint) -> (TypeScheme, MConstraint)
        tightenElem (scheme, vConstraint) = (scheme, vConstraint %/ constraint)

contextLookup :: Context -> SourceLocation -> Identifier -> Checker Type
contextLookup ctx loc name = case M.lookup name (ctx ^. termContext) of
                               Nothing -> typeError $ VariableNotInScope loc name
                               Just (scheme, constraint) -> do
                                   checkAndConsume constraint
                                   instantiate scheme
    where
        checkAndConsume :: MConstraint -> Checker ()
        checkAndConsume (MConstraint allowedAffine allowedRelevant) = do
            -- If the variable we are trying to use is in the zero set, it cannot be consumed.
            isZeroed <- checkInSet zeroVars
            when isZeroed $ typeError $ AffinityViolation loc name
            -- If the variable is affine constrained, but affine variables cannot be used in the constraint
            -- context, then throw
            isAffine <- checkInSet affineVars
            when (isAffine && not allowedAffine) $ typeError $ ContextAffinityViolation loc name
            -- If the variable is relevant, but relevant variables cannot be used, then throw
            isRelevant <- checkInSet relevantVars
            when (isRelevant && not allowedRelevant) $ typeError $ ContextRelevancyViolation loc name

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
        instantiate (TypeScheme vars t) = do
            freshVars <- mapM (const freshVarType) vars
            pure $ substitute (M.fromList (zip vars freshVars)) t

freshVar :: Checker TypeVar
freshVar = do
    (var Stream.:> rest) <- gets (^. freshTypeVars)
    modify (freshTypeVars .~ rest)
    pure var

freshVarType :: Checker Type
freshVarType = Poly <$> freshVar

-- TODO: Add scoped type variables

annotationToType :: Annotated a -> Checker Type
annotationToType (Annotated _ Nothing) = freshVarType
annotationToType (Annotated _ (Just t)) = createTypeFor (syntax t)

createArrowFor :: ArrowExpr -> Checker Arrow
createArrowFor (ArrowExpr Nothing) = pure (Arrow Nothing)
createArrowFor (ArrowExpr (Just m)) = pure (Arrow (Just (syntax m)))

createTypeFor :: TypeExpr -> Checker Type
createTypeFor (TEGround name) = pure (Ground name)
createTypeFor (TEPoly poly) = do
    newTypeVar <- freshVar
    modify (varAssignments %~ M.insert newTypeVar poly)
    pure (Poly newTypeVar) 
createTypeFor (TEApp con arg) = do
    conType <- createTypeFor (syntax con)
    argType <- createTypeFor (syntax arg)
    pure (TypeApp conType argType)
createTypeFor (TEArrow from arrow to) = do
    fromType <- createTypeFor (syntax from)
    toType <- createTypeFor (syntax to)
    arrowType <- createArrowFor (syntax arrow)
    pure (FunctionType fromType arrowType toType)
createTypeFor TEUnit = pure unitType
createTypeFor (TETuple ts) = do
    tupleTypes <- mapM (createTypeFor . syntax) ts
    pure (TupleType tupleTypes)
createTypeFor (TEList t) = TypeApp listTypeCon <$> createTypeFor (syntax t)

mgu :: SourceLocation -> Type -> Type -> Checker SubMap
mgu loc (Poly p) t = bindTypeVar loc p t
mgu loc t (Poly p) = bindTypeVar loc p t
mgu loc (Ground g) (Ground g') -- TODO: Maybe handle this better than just with string equality
    | g == g' = pure emptySub
    | otherwise = typeError $ GroundUnificationFailure loc g g'
mgu loc (TypeApp con arg) (TypeApp con' arg') = do
    s0 <- mgu loc con con'
    s1 <- mgu loc (substitute s0 arg) (substitute s0 arg')
    pure (s1 `M.union` s0)
mgu loc (FunctionType from _ to) (FunctionType from' _ to') = do -- TODO: think about arrow types?
    s0 <- mgu loc from from'
    s1 <- mgu loc (substitute s0 to) (substitute s0 to')
    pure (s1 `M.union` s0)
mgu loc (TupleType ts) (TupleType ts') = foldM combinator emptySub (zip ts ts')
    where
        combinator :: SubMap -> (Type, Type) -> Checker SubMap
        combinator s (t, t') = M.union s <$> mgu loc (substitute s t) (substitute s t')
mgu loc t t' = typeError $ UnificationFailure loc t t'

checkTypeEntails :: Context -> Type -> Maybe (Loc TypeExpr) -> Checker SubMap
checkTypeEntails _ inferredType Nothing = pure emptySub
checkTypeEntails ctx inferredType (Just ann) = entails inferredType ann
    where
        ctxFtvs :: S.HashSet TypeVar
        ctxFtvs = ftv ctx

        entails :: Type -> Loc TypeExpr -> Checker SubMap
        entails t@(Poly p) expr 
            | p `S.member` ctxFtvs = typeError $ EntailmentFailure (location expr) t
            | otherwise = do
                exprType <- createTypeFor (syntax expr)
                pure (M.singleton p exprType)
        entails t@(Ground name) (L loc (TEGround name'))
            | name == name' = pure emptySub
            | otherwise = typeError $ EntailmentFailure loc t
        entails t@(Ground _) (L loc TEUnit)
            | t == unitType = pure emptySub
            | otherwise = typeError $ EntailmentFailure loc t
        entails (TypeApp con arg) (L _ (TEApp con' arg')) = do
            conSub <- entails con con'
            argSub <- entails (substitute conSub arg) arg'
            pure (conSub `M.union` argSub)
        entails t@(TypeApp listCon listArg) (L loc (TEList list))
            | listCon == listCon = entails listArg list
            | otherwise = typeError $ EntailmentFailure loc t
        entails t@(FunctionType from (Arrow mul) to) (L loc (TEArrow from' (L _ (ArrowExpr mul')) to'))
            | mul == (syntax <$> mul') = do
                fromSub <- entails from from'
                toSub <- entails (substitute fromSub to) to'
                pure (fromSub `M.union` toSub)
            | otherwise = typeError $ EntailmentFailure loc t
        entails (TupleType ts) (L _ (TETuple ts')) = do
            foldM combinator emptySub (zip ts ts')
            where
                combinator :: SubMap -> (Type, Loc TypeExpr) -> Checker SubMap
                combinator sub (t, t') = entails (substitute sub t) t'
        entails t (L loc _) = typeError $ EntailmentFailure loc t


bindTypeVar :: SourceLocation -> TypeVar -> Type -> Checker SubMap
bindTypeVar loc var t@(Poly var')
    | var == var' = pure emptySub
    | otherwise = pure (M.singleton var t)
bindTypeVar loc var t
    | var `S.member` ftv t = typeError $ OccursCheckFailure loc var t
    | otherwise = pure (M.singleton var t)

constraintFor :: MultiplicityAtom -> MConstraint
constraintFor Normal = MConstraint False False
constraintFor Linear = MConstraint True True
constraintFor Relevant = MConstraint False True
constraintFor Affine = MConstraint True False

infixl 7 %/
(%/) :: MConstraint -> MConstraint -> MConstraint
(MConstraint a r) %/ (MConstraint a' r') = MConstraint (a && a') (r && r')

infixl 5 +.
(+.) :: SubMap -> SubMap -> SubMap
s1 +. s0 = M.map (substitute s1) s0 <> s1

