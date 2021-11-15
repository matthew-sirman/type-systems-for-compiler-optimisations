module Typing.Checker where

import Parser.AST
import Parser.Parser (test_parseExpr)
import Typing.Types
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

-- type RemapperState a = StateT (M.HashMap Identifier TypeVar) CheckerState a

typecheck :: StaticContext -> Loc ValExpr -> Either (TypeError, TypeVarMap) Type
typecheck expr = runReader (evalState (runExceptT checker) emptyCheckState)
    where
        checker :: Checker Type
        checker = fst <$> typecheck' emptyContext expr

-- typecheck expr = flip evalState emptyCheckState $ do
--     -- We construct a new state monad within this evalState call. Then, we
--     -- evaluate the entire monad under the empty check state. Doing this nested
--     -- monadic evaluation allows us to feed the alterations made to the initial
--     -- check state into the main type checker.
--     --
--     -- First, we "remap" the expression. That is, we take each type variable in
--     -- the expression and map it to a unique fresh type variable index. This
--     -- is done such that if "a" in the source maps to variable index n, then each
--     -- instance of "a" maps to the same n.
--     remappedExpr <- remapVars M.empty expr
--     -- After remapping the variables, we run the type checker. This is wrapped in
--     -- an except monad to capture any failures in type checking, so we run the
--     -- except monad at this level.
--     --
--     -- We start with the empty variable context, and the remapped expression.
--     -- Note that we start with linear constraints on the function. This is because
--     -- we define under the assumption that this function will be used once.
--     -- In other words, we are proving the properties about different variables
--     -- in the instance that the function result is consumed exactly once.
--     (remapTypeVars <$>) <$> runExceptT (fst <$> typecheck' emptyContext remappedExpr)
--     where
--         -- The remapVars function works by taking in a top level context, which maps
--         -- variable names to their type variable identifier. This context is fed
--         -- through each layer in the tree, such that type variables are scoped.
--         -- So, for example, in an expression like
--         --  let x : a = e in let y : a = e' in e''
--         -- the two instances of "a" will map to different type variables, as they
--         -- logically are different.
--         -- But, in the expression
--         --  let x : a = let y : a = e in e' in e''
--         -- the two instances of "a" will map to the same type variable, as they are
--         -- logically considered the same.
--         --
--         -- Further, we have the expexted property that in an expression
--         --  let x : a -> a = e in e'
--         -- we have the two "a"s mapping to the same type variable.
--         remapVars :: M.HashMap Identifier TypeVar -> ValExpr Identifier 
--                   -> CheckerState (ValExpr TypeVar)
-- 
--         remapVars ctx (VELet bindings body sl) = do
--             VELet <$> mapM remapBinding bindings <*> remapVars ctx body <*> pure sl
--             where
--                 remapBinding :: LetBinding Identifier 
--                              -> CheckerState (LetBinding TypeVar)
--                 remapBinding (LetBinding m pattern expr) = do
--                     (pattern', boundCtx) <- runStateT (traverse remap pattern) ctx
--                     LetBinding m pattern' <$> remapVars boundCtx expr
--         remapVars ctx (VECase m disc branches sl) =
--             VECase m <$> remapVars ctx disc <*> traverse remapBranch branches <*> pure sl
--             where
--                 remapBranch :: CaseBranch Identifier -> CheckerState (CaseBranch TypeVar)
--                 remapBranch (CaseBranch pattern expr) = CaseBranch pattern <$> remapVars ctx expr
--         remapVars ctx (VEApp fun arg sl) =
--             VEApp <$> remapVars ctx fun <*> remapVars ctx arg <*> pure sl
--         remapVars ctx (VELambda pattern arrow body sl) = do
--             (pattern', boundCtx) <- runStateT (traverse remap pattern) ctx
--             VELambda pattern' arrow <$> remapVars boundCtx body <*> pure sl
--         remapVars _ (VEVar v sl) = pure (VEVar v sl)
--         remapVars ctx (VELiteral literal sl) =
--             VELiteral <$> traverse (remapVars ctx) literal <*> pure sl
-- 
--         -- Remap an individual variable name to a type variable
--         remap :: Identifier -> RemapperState TypeVar
--         remap name = do
--             -- Get the current mapping
--             mapped <- gets (M.lookup name)
--             case mapped of
--               -- If the variable is currently unmapped, then create
--               -- a fresh variable, insert it into the map and return it
--               Nothing -> do
--                   v <- lift freshVar
--                   modify (M.insert name v)
--                   pure v
--               -- Otherwise just return the variable
--               Just var -> pure var
-- 
--         -- This function takes a type expression which has numeric values for type variables, and
--         -- maps it into an expression which uses named identifiers instead
--         --
--         -- TODO: Reverse the mapping from above in the case that the code explicitly stated a type
--         -- variable which has now been given a new name
--         -- TODO: Consider whether this is actually the correct place to have this inverse mapping
--         remapTypeVars :: TypeExpr TypeVar -> TypeExpr Identifier
--         remapTypeVars expr = evalState (traverse remapOne expr) (M.empty, varNameStream)
--             where
--                 remapOne :: TypeVar -> State (M.HashMap TypeVar Identifier, Stream.Stream String) Identifier
--                 remapOne var = do
--                     -- Get the current mapping and get the head of the stream
--                     (varMap, name Stream.:> names) <- get
--                     -- Check if the variable has already been mapped
--                     case M.lookup var varMap of
--                       Nothing -> do
--                           -- If not, then insert the variable into the mapping and
--                           -- update the stream to include only the tail
--                           put (M.insert var name varMap, names)
--                           -- Return the name
--                           pure name
--                       -- Otherwise just return the name
--                       Just name' -> pure name'
--         
--         -- An infinite stream of variable names which looks like
--         --  a, b, c, ..., x, y, z, a', b', .. y', z', a'', b'', ...
--         varNameStream :: Stream.Stream String
--         varNameStream = vns' (map pure "abcdefghijklmnopqrstuvwxyz")
--             where
--                 vns' :: [String] -> Stream.Stream String
--                 vns' names = build names
--                     where
--                         build :: [String] -> Stream.Stream String
--                         build [] = vns' (map (++ "'") names)
--                         build (n:ns) = n Stream.:> build ns

-- Typecheck and infer the type of an expression under a given variable context.
typecheck' :: Context -> Loc ValExpr -> Checker (Type, SubMap)

typecheck' ctx (L _ (VELet bindings body)) = do
    -- Check each let binding and get a list of their constriants, patterns and types,
    -- along with a substitution for all the learned information from checking them
    (ctx', extensions, s0) <- checkLetBindings
    -- Extend the context with the generalised types we inferred
    (ctx'', s2, checkRelevant) <- extendGeneralise ctx' extensions
    -- Typecheck the body under the extended context
    (bodyType, s1) <- typecheck' ctx'' body
    -- Check that any relevant variables introduced are now consumed
    checkRelevant
    pure (substitute s2 bodyType, s1 +. s0)
    where
        checkLetBindings :: Checker (Context, [(MConstraint, Loc Pattern, Type)], SubMap)
        checkLetBindings = do
            let projectAnnotation (LetBinding _ ann _) = syntax ann
                annotatedPatterns = map (projectAnnotation . syntax) bindings
                patterns = map (\(Annotated pattern _) -> pattern) annotatedPatterns

            -- We create new type variables for each of the annotated patterns
            initialBoundTypes <- mapM annotationToType annotatedPatterns
            -- We extend the context with the new type variables in order to type check the
            -- bound expressions
            --
            -- We always extend with normal multiplicity for recursive function bindings.
            (ctx', extendSub, _) <- extendNormal ctx (zip3 (repeat $ constraintFor Normal) patterns initialBoundTypes)
            -- Next, we fold over checking each binding to get a (reversed) list of the types we inferred,
            -- and a substitution we "learned" from checking each binding.
            foldM checkBinding (ctx', [], emptySub) (zip (map syntax bindings) (map (substitute extendSub) initialBoundTypes))

        checkBinding :: (Context, [(MConstraint, Loc Pattern, Type)], SubMap)
                     -> (LetBinding, Type)
                     -> Checker (Context, [(MConstraint, Loc Pattern, Type)], SubMap)
        checkBinding (ctx', types, sub) (binding, initialBoundType) = do
            let (LetBinding m (L loc (Annotated pattern patType)) bound) = binding
            letM <- getMul loc m
            let constraint = constraintFor letM
            -- We need to tighten the context constraints for the bound expression - these must be 
            -- extended to account for the the fact that the newly bound variable could have a 
            -- weaker multiplicity than one of the values it depends on - this cannot be allowed,
            -- as we could then indirectly violate the multiplicity constraint. So, we tighten
            -- the context to prevent stronger values from being used incorrectly
            (boundType, s0) <- typecheck' (tighten ctx' constraint) bound
            -- subBoundType <- mgu (location bound) boundType (substitute s0 initialBoundType)
            -- Check that if there was an explicit annotation, that the type we inferred unifies with it.
            -- If there was an annotation, and we have inferred a type which proves the annotation is
            -- appropriate, then we should just use the annotation
            -- !!!! entailSub <- checkTypeEntails (substitute subBoundType boundType) patType
            entailSub <- checkTypeEntails ctx' boundType patType
            -- Update the context for the new substitution for checking the next binding
            -- Add the constraint pattern type triple for this binding
            -- Update the substitution
            pure (substitute (entailSub +. s0) ctx', (constraint, pattern, substitute entailSub boundType) : types, entailSub +. s0 +. sub)

            where
                getMul :: SourceLocation -> Maybe (Loc Multiplicity) -> Checker MultiplicityAtom
                getMul _ (Just (L _ (MAtom letM))) = pure letM
                getMul loc _ = typeError $ GenericError (Just loc) "Let binding must be explicitly annotated with a concrete multiplicity (for now)."

typecheck' ctx (L _ (VECase (Just (L _ (MAtom caseM))) disc branches)) = do
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
    initialBranchType <- freshVarType
    (_, exprType, _, sOut, (outA, outR, outZ)) <- foldM (compareBranches resetter)
                                                        (discType, initialBranchType, substitute s0 ctx, s0, vSets)
                                                        branches
    lift $ modify ( (affineVars .~ outA)
                  . (relevantVars .~ outR)
                  . (zeroVars .~ outZ) )
    pure (exprType, sOut)
    where
        compareBranches :: Checker ()
                        -> (Type, Type, Context, SubMap, (VarSet, VarSet, VarSet))
                        -> Loc CaseBranch
                        -> Checker (Type, Type, Context, SubMap, (VarSet, VarSet, VarSet))

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
            (branchType', s0) <- checkBranch bCtx discType (syntax branch)
            -- Now we unify our updated view of the previously expected branch type with the newly
            -- inferred branch type.
            s1 <- mgu (location branch) (substitute s0 branchType) branchType'
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

            pure ( substitute s0 discType
                 , substitute s1 branchType'
                 , substitute s0 bCtx
                 , s0 +. inSub
                 , (outA, outR, outZ))

        checkBranch :: Context -> Type -> CaseBranch -> Checker (Type, SubMap)

        checkBranch bCtx discType (CaseBranch pattern body) = do
            -- Extend the context with the pattern under the constraint provided by the case statement
            (bCtx', discSub, checkRelevant) <- extendNormal bCtx [(constraintFor caseM, pattern, discType)]
            -- Check the branch itself
            (branchType, branchSub) <- typecheck' (substitute discSub bCtx') body
            -- Check that any relevant variables introduced within the branch itself have been consumed
            checkRelevant
            pure (branchType, branchSub +. discSub)

        getVarSets :: Checker (VarSet, VarSet, VarSet)
        getVarSets = do
            preBranchState <- lift get
            let inA = preBranchState ^. affineVars
                inR = preBranchState ^. relevantVars
                inZ = preBranchState ^. zeroVars
            pure (inA, inR, inZ)

typecheck' _ (L loc (VECase {})) =
    typeError $ GenericError (Just loc) "Case expression must be explicitly annotated with a concrete multiplicity (for now)."

typecheck' ctx (L _ (VEApp fun arg)) = do
    (funType, s0) <- typecheck' ctx fun 
    -- (from, arrowMul, to) <- unpack funType

    (argType, s1) <- typecheck' (substitute s0 (tighten ctx (constraintFor (unpackMul funType)))) arg

    returnType <- freshVarType
    s2 <- mgu (location fun) (substitute s1 funType) (FunctionType argType (Arrow Nothing) returnType)

    pure (substitute s2 returnType, s2 +. s1 +. s0)

    where
        -- unpack :: TypeExpr TypeVar -> Checker (TypeExpr TypeVar, MultiplicityAtom, TypeExpr TypeVar)
        -- unpack (TEArrow from (Arrow (Just (MAtom m))) to) = pure (from, m, to)
        -- unpack _ = throwError "Function in application must have function type with explicit concrete multiplicity."
        unpackMul :: Type -> MultiplicityAtom
        unpackMul (FunctionType _ (Arrow (Just (MAtom m))) _) = m
        unpackMul _ = Normal

typecheck' ctx (L _ (VELambda (L _ ann@(Annotated pattern patType)) (L _ arrow@(ArrowExpr (Just (L _ (MAtom arrowMul))))) body)) = do
    argType <- annotationToType ann
    (ctx', argSub, checkRelevant) <- extendNormal ctx [(constraintFor arrowMul, pattern, argType)]
    (bodyType, s) <- typecheck' ctx' body
    let argType' = substitute (s +. argSub) argType
    entailSub <- checkTypeEntails ctx argType' patType
    checkRelevant
    arrow' <- createArrowFor arrow
    pure (FunctionType (substitute entailSub argType') arrow' (substitute entailSub bodyType), s)

typecheck' _ (L loc (VELambda {})) =
    typeError $ GenericError (Just loc) "Lambda expression must be explicitly annotated with a concrete multiplicity (for now)."

typecheck' ctx (L loc (VEVar x)) = do
    varType <- contextLookup ctx loc x
    pure (varType, emptySub)

typecheck' ctx (L _ (VELiteral lit)) = typecheckLiteral ctx lit

typecheckLiteral :: Context -> Literal (Loc ValExpr) -> Checker (Type, SubMap)
typecheckLiteral _ (IntLiteral _) = pure (intType, emptySub)

typecheckLiteral _ (RealLiteral _) = pure (realType, emptySub)

typecheckLiteral ctx (ListLiteral es) = do
    initialListType <- freshVarType
    (listType, sub, _) <- foldM combinator (initialListType, emptySub, ctx) es
    pure (TypeApp listTypeCon listType, sub)
    where
        combinator :: (Type, SubMap, Context) -> Loc ValExpr -> Checker (Type, SubMap, Context)
        combinator (t, s, ctx') expr = do
            (t', s0) <- typecheck' ctx' expr
            s1 <- mgu (location expr) (substitute s0 t) t'
            pure (substitute s1 t', s1 +. s, substitute s0 ctx')

typecheckLiteral ctx (TupleLiteral exprs) = do
    (types, sub, _) <- foldM combinator ([], emptySub, ctx) exprs
    pure (TupleType (reverse types), sub)
    where
        combinator :: ([Type], SubMap, Context) -> Loc ValExpr -> Checker ([Type], SubMap, Context)
        combinator (types, s, ctx') expr = do
            (t, s') <- typecheck' ctx' expr
            pure (t : types, s' +. s, substitute s' ctx')

testEverything :: String -> IO ()
testEverything s = case typecheck (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (showError s tvm e)
                     Right t -> print t
    where
        fromRight (Right x) = x

