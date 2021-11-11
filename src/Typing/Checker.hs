module Typing.Checker where

import Parser.Parser
import Typing.Judgement
import qualified Util.Stream as Stream

import Control.Monad.Except
import Control.Monad.State
import Control.Lens hiding (Context)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (isNothing)
import Data.Functor (($>))
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

type RemapperState a = StateT (M.HashMap Identifier TypeVar) CheckerState a

typecheck :: ValExpr Identifier -> Either String (TypeExpr Identifier)
typecheck expr = flip evalState emptyCheckState $ do
    -- We construct a new state monad within this evalState call. Then, we
    -- evaluate the entire monad under the empty check state. Doing this nested
    -- monadic evaluation allows us to feed the alterations made to the initial
    -- check state into the main type checker.
    --
    -- First, we "remap" the expression. That is, we take each type variable in
    -- the expression and map it to a unique fresh type variable index. This
    -- is done such that if "a" in the source maps to variable index n, then each
    -- instance of "a" maps to the same n.
    remappedExpr <- remapVars M.empty expr
    -- After remapping the variables, we run the type checker. This is wrapped in
    -- an except monad to capture any failures in type checking, so we run the
    -- except monad at this level.
    --
    -- We start with the empty variable context, and the remapped expression.
    -- Note that we start with linear constraints on the function. This is because
    -- we define under the assumption that this function will be used once.
    -- In other words, we are proving the properties about different variables
    -- in the instance that the function result is consumed exactly once.
    (remapTypeVars <$>) <$> runExceptT (fst <$> typecheck' emptyContext remappedExpr)
    where
        -- The remapVars function works by taking in a top level context, which maps
        -- variable names to their type variable identifier. This context is fed
        -- through each layer in the tree, such that type variables are scoped.
        -- So, for example, in an expression like
        --  let x : a = e in let y : a = e' in e''
        -- the two instances of "a" will map to different type variables, as they
        -- logically are different.
        -- But, in the expression
        --  let x : a = let y : a = e in e' in e''
        -- the two instances of "a" will map to the same type variable, as they are
        -- logically considered the same.
        --
        -- Further, we have the expexted property that in an expression
        --  let x : a -> a = e in e'
        -- we have the two "a"s mapping to the same type variable.
        --
        remapVars :: M.HashMap Identifier TypeVar -> ValExpr Identifier 
                  -> CheckerState (ValExpr TypeVar)

        remapVars ctx (VELet m pattern bound body) = do
            (pattern', boundCtx) <- runStateT (traverse remap pattern) ctx
            VELet m pattern' <$> remapVars boundCtx bound <*> remapVars ctx body
        remapVars ctx (VECase m disc branches) =
            VECase m <$> remapVars ctx disc <*> traverse remapBranch branches
            where
                remapBranch :: CaseBranch Identifier -> CheckerState (CaseBranch TypeVar)
                remapBranch (CaseBranch pattern expr) = CaseBranch pattern <$> remapVars ctx expr
        remapVars ctx (VEApp fun arg) =
            VEApp <$> remapVars ctx fun <*> remapVars ctx arg
        remapVars ctx (VELambda pattern arrow body) = do
            (pattern', boundCtx) <- runStateT (traverse remap pattern) ctx
            VELambda pattern' arrow <$> remapVars boundCtx body
        remapVars _ (VEVar v) = pure (VEVar v)
        remapVars ctx (VELiteral literal) =
            VELiteral <$> traverse (remapVars ctx) literal

        -- Remap an individual variable name to a type variable
        remap :: Identifier -> RemapperState TypeVar
        remap name = do
            -- Get the current mapping
            mapped <- gets (M.lookup name)
            case mapped of
              -- If the variable is currently unmapped, then create
              -- a fresh variable, insert it into the map and return it
              Nothing -> do
                  v <- lift freshVar
                  modify (M.insert name v)
                  pure v
              -- Otherwise just return the variable
              Just var -> pure var

        remapTypeVars :: TypeExpr TypeVar -> TypeExpr Identifier
        remapTypeVars expr = evalState (traverse remapOne expr) (M.empty, varNameStream)
            where
                remapOne :: TypeVar -> State (M.HashMap TypeVar Identifier, Stream.Stream String) Identifier
                remapOne var = do
                    (varMap, name Stream.:> names) <- get
                    case M.lookup var varMap of
                      Nothing -> do
                          put (M.insert var name varMap, names)
                          pure name
                      Just name' -> pure name'
        
        varNameStream :: Stream.Stream String
        varNameStream = vns' (map pure "abcdefghijklmnopqrstuvwxyz")
            where
                vns' :: [String] -> Stream.Stream String
                vns' names = build names
                    where
                        build :: [String] -> Stream.Stream String
                        build [] = vns' (map (++ "'") names)
                        build (n:ns) = n Stream.:> build ns

typecheck' :: Context -> ValExpr TypeVar -> Checker (TypeExpr TypeVar, SubMap)

typecheck' ctx (VELet (Just (MAtom letM)) (Annotated pattern patType) bound body) = do
    -- Get the type for the bound expression.
    -- We need to tighten the context constraints for the bound expression - these must be 
    -- extended to account for the the fact that the newly bound variable could have a 
    -- weaker multiplicity than one of the values it depends on - this cannot be allowed,
    -- as we could then indirectly violate the multiplicity constraint. So, we tighten
    -- the context to prevent stronger values from being used incorrectly
    (boundType, s0) <- typecheck' (tighten ctx (constraintFor letM)) bound
    -- Check that, if there is an annotated type, the bound type can specialise to it
    checkTypeMatch patType boundType "Bound type in let expression does not unify with annotation."
    -- Extend the context with the new variables brought into scope, putting their multiplicities
    -- as whatever constraint the let binding has
    (ctx', s2, checkRelevant) <- extend True (substitute s0 ctx) (constraintFor letM) pattern boundType
    -- Type check the body expression with the same constraint set as the whole expression has
    -- but under the extended context.
    (bodyType, s1) <- typecheck' ctx' body
    -- Check that any relevant variables introduced are now consumed
    checkRelevant
    pure (substitute s2 bodyType, s1 +. s0)

typecheck' _ (VELet {}) =
    throwError "Let binding must be explicitly annotated with a concrete multiplicity (for now)."

typecheck' ctx (VECase (Just (MAtom caseM)) disc branches) = do
    -- Check the discriminator
    -- We need to tighten constraints for the discriminator expression - these are extended to account
    -- for the fact that we will destruct the discriminator `caseM` times - so if `caseM` is
    -- a weaker multiplicity than the current constraint, we must tighten.
    (discType, s0) <- typecheck' (tighten ctx (constraintFor caseM)) disc

    -- Get the variable constraint sets. These must be folded through the branches to check
    -- how each branch uses them.
    vSets@(inA, inR, inZ) <- getVarSets
    -- Here, we create a state monad "resetter" designed to reset only these variable sets to
    -- what they are at this point in execution. When this resetter is used later, the variables
    -- will reset to this state. This allows us to have the same variable set when entering
    -- each branch of the case: modifications in one branch will not persist to other branches,
    -- as only one branch is ever executed.
    let resetter = lift $ modify ( (affineVars .~ inA) 
                                 . (relevantVars .~ inR)
                                 . (zeroVars .~ inZ) )

    -- We also want to fold through a result type for the branches. Initially, we have no idea
    -- what type the branches will result in, so we just create a fresh polymorphic variable.
    -- The idea is that after each branch is typed, we will use the most general unifier between
    -- the current best type, and the type we have just seen for this branch. Then, we will feed
    -- this newly unified type onto the next branch.
    initialBranchType <- TEPoly <$> lift freshVar
    (exprType, _, _, sOut, (outA, outR, outZ)) <- foldM (compareBranches resetter)
                                                        (discType, initialBranchType, substitute s0 ctx, s0, vSets)
                                                        branches
    lift $ modify ( (affineVars .~ outA)
                  . (relevantVars .~ outR)
                  . (zeroVars .~ outZ) )
    pure (exprType, sOut)
    where
        compareBranches :: Checker ()
                        -> (TypeExpr TypeVar, TypeExpr TypeVar, Context, SubMap, (VarSet, VarSet, VarSet))
                        -> CaseBranch TypeVar
                        -> Checker (TypeExpr TypeVar, TypeExpr TypeVar, Context, SubMap, (VarSet, VarSet, VarSet))

        compareBranches resetVarSets (discType, branchType, bCtx, inSub, (inA, inR, inZ)) branch = do
            -- At the start of the branch, we reset the variable states
            resetVarSets
            -- Then, we actually check the branch. This returns firstly the type we infer from the
            -- branch
            -- Next, we get a unifier for extending the context for this branch. This is because the
            -- discriminator may have resulted in a type which we learn more about when we actually
            -- decompose it.
            -- Finally, we return a context substitution for the branch inference. This is what we
            -- learned about any type variables through typing the branch.
            (branchType', discSub, s0) <- checkBranch bCtx discType branch
            -- Now we unify our updated view of the previously expected branch type with the newly
            -- inferred branch type.
            s1 <- mgu (substitute s0 branchType) branchType'

            -- Next, we handle the affine relevant and zero set tracking.
            (bA, bR, bZ) <- getVarSets

            -- We can see here that we fold each set through with either an intersection or union.
            --
            -- Affine
            --  The affine variables are intersected with one another. This is to say that if an affine
            -- variable is used on any case branch, then it must not be used after the case expression.
            -- This is essential as we cannot know which branch is taken at typing, so we cannot use it
            -- anywhere else in the program. So, by taking the intersection of the remaining affine
            -- variables, we keep only those which were not used in any branch.
            --
            -- Relevant
            --  Here, we take the union. This is because we may only drop the relevant constraint for a
            -- variable if it is used in every branch, otherwise we cannot be sure that it was used. So,
            -- the only way a relevant variable remains is if it was not used in every branch.
            --
            -- Zero
            --  Again, we take the union. One way to think of this is that the union of affine and zero
            -- variables should be invariant. Another way to think about it is that if a variable is moved
            -- to the zero set among any branch, then it cannot be used in the rest of the program, as that
            -- branch may be decided. So, we must place it in the zero branch.
            --
            -- It is interesting to note that if a linear variable is used in some branches but not others,
            -- then it will end up in the zero set and the relevant set. However, this is guaranteed to fail:
            -- the relevant set says we must use the variable to not experience an error, but the zero set
            -- says we cannot use it. But this is exactly the property we want for linear variables.
            let outA = inA `S.intersection` bA
                outR = inR `S.union` bR
                outZ = inZ `S.union` bZ

            pure ( substitute discSub discType
                 , substitute s1 branchType'
                 , substitute s0 bCtx
                 , s0 +. inSub
                 , (outA, outR, outZ))

        checkBranch :: Context -> TypeExpr TypeVar -> CaseBranch TypeVar
                    -> Checker (TypeExpr TypeVar, SubMap, SubMap)

        checkBranch bCtx discType (CaseBranch pattern body) = do
            -- Extend the context with the pattern under the constraint provided by the case statement
            (bCtx', discSub, checkRelevant) <- extend False bCtx (constraintFor caseM) pattern discType
            -- Check the branch itself
            (branchType, branchSub) <- typecheck' bCtx' body
            -- Check that any relevant variables introduced within the branch itself have been consumed
            checkRelevant
            pure (branchType, discSub, branchSub)

        getVarSets :: Checker (VarSet, VarSet, VarSet)
        getVarSets = do
            preBranchState <- lift get
            let inA = preBranchState ^. affineVars
                inR = preBranchState ^. relevantVars
                inZ = preBranchState ^. zeroVars
            pure (inA, inR, inZ)

typecheck' _ (VECase {}) =
    throwError "Case expression must be explicitly annotated with a concrete multiplicity."

typecheck' ctx (VEApp fun arg) = do
    (funType, s0) <- typecheck' ctx fun 
    -- (from, arrowMul, to) <- unpack funType

    (argType, s1) <- typecheck' (substitute s0 (tighten ctx (constraintFor (unpackMul funType)))) arg

    returnType <- TEPoly <$> lift freshVar
    s2 <- mgu (substitute s1 funType) (TEArrow argType (Arrow Nothing) returnType)

    pure (substitute s2 returnType, s2 +. s1 +. s0)

    where
        -- unpack :: TypeExpr TypeVar -> Checker (TypeExpr TypeVar, MultiplicityAtom, TypeExpr TypeVar)
        -- unpack (TEArrow from (Arrow (Just (MAtom m))) to) = pure (from, m, to)
        -- unpack _ = throwError "Function in application must have function type with explicit concrete multiplicity."
        unpackMul :: TypeExpr TypeVar -> MultiplicityAtom
        unpackMul (TEArrow _ (Arrow (Just (MAtom m))) to) = m
        unpackMul _ = Normal

typecheck' ctx (VELambda (Annotated pattern patType) arrow@(Arrow (Just (MAtom arrowMul))) body) = do
    argType <- TEPoly <$> lift freshVar
    (ctx', argSub, checkRelevant) <- extend False ctx (constraintFor arrowMul) pattern argType
    (bodyType, s) <- typecheck' ctx' body
    let argType' = substitute (s +. argSub) argType
    checkTypeMatch patType argType' "Bound type in let expression does not unify with annotation."
    checkRelevant
    pure (TEArrow argType' arrow bodyType, s)

typecheck' _ (VELambda {}) =
    throwError "Lambda expression must be explicitly annotated with a concrete multiplicity."

typecheck' ctx (VEVar x) =
    (,) <$> contextLookup ctx x <*> pure emptySub

typecheck' _ (VELiteral (IntLiteral _)) = pure (TEGround "Int", emptySub)

typecheck' _ (VELiteral (RealLiteral _)) = pure (TEGround "Real", emptySub)

typecheck' ctx (VELiteral (ListLiteral es)) = do
    initialListType <- TEPoly <$> lift freshVar
    (listType, sub, _) <- foldM combinator (initialListType, emptySub, ctx) es
    pure (TEList listType, sub)
    where
        combinator :: (TypeExpr TypeVar, SubMap, Context) -> ValExpr TypeVar -> Checker (TypeExpr TypeVar, SubMap, Context)
        combinator (t, s, ctx') expr = do
            (t', s0) <- typecheck' ctx' expr
            s1 <- mgu (substitute s0 t) t'
            pure (substitute s1 t', s1 +. s, substitute s0 ctx')

typecheck' ctx (VELiteral (TupleLiteral exprs)) = do
    (types, sub, _) <- foldM combinator ([], emptySub, ctx) exprs
    pure (TETuple (reverse types), sub)
    where
        combinator :: ([TypeExpr TypeVar], SubMap, Context) -> ValExpr TypeVar -> Checker ([TypeExpr TypeVar], SubMap, Context)
        combinator (types, s, ctx') expr = do
            (t, s') <- typecheck' ctx' expr
            pure (t : types, s' +. s, substitute s' ctx')

checkTypeMatch :: Maybe (TypeExpr TypeVar) -> TypeExpr TypeVar -> String -> Checker ()
checkTypeMatch Nothing _ _ = pure ()
checkTypeMatch (Just t) t' errorMessage = catchError (mgu t t' $> ()) (const (throwError errorMessage))

mgu :: TypeExpr TypeVar -> TypeExpr TypeVar -> Checker SubMap
mgu (TEPoly p) t = bindTypeVar p t
mgu t (TEPoly p) = bindTypeVar p t
mgu (TEGround g) (TEGround g') -- TODO: Maybe handle this better than just with string equality
  | g == g' = pure emptySub
  | otherwise = throwError $ "Cannot unify '" ++ g ++ "' with '" ++ g' ++ "'."
mgu (TEApp con arg) (TEApp con' arg') = do
    s0 <- mgu con con'
    s1 <- mgu (substitute s0 arg) (substitute s0 arg')
    pure (s1 `M.union` s0)
mgu (TEArrow from _ to) (TEArrow from' _ to') = do -- TODO: think about arrow types?
    s0 <- mgu from from'
    s1 <- mgu (substitute s0 to) (substitute s0 to')
    pure (s1 `M.union` s0)
mgu TEUnit TEUnit = pure emptySub
mgu (TETuple ts) (TETuple ts') = foldM combinator emptySub (zip ts ts')
    where
        combinator :: SubMap -> (TypeExpr TypeVar, TypeExpr TypeVar) -> Checker SubMap
        combinator s (t, t') = M.union s <$> mgu (substitute s t) (substitute s t')
mgu (TEList t) (TEList t') = mgu t t'
mgu t t' = throwError $ "Unification '" ++ show t ++ " ~ " ++ show t' ++ "' failed."

bindTypeVar :: TypeVar -> TypeExpr TypeVar -> Checker SubMap
bindTypeVar var t@(TEPoly var')
    | var == var' = pure emptySub
    | otherwise = pure (M.singleton var t)
bindTypeVar var typeExpr
    | var `S.member` ftv typeExpr = throwError $ "Occurs check for '" ++ show var ++ "' failed."
    | otherwise = pure (M.singleton var typeExpr)

