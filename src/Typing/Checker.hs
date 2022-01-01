module Typing.Checker where

import Parser.AST
import Parser.Parser (test_parseExpr)
import Typing.Types
import Typing.Judgement
import qualified Util.Stream as Stream

import qualified Builtin.Builtin as B
import qualified Builtin.Types as B

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Context)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (isNothing)
import Data.Functor (($>))
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

-- TODO: REMOVE
import qualified Data.DisjointSet as DS
import Typing.Types (CheckVarFrame(CheckVarFrame))

-- type RemapperState a = StateT (M.HashMap Identifier TypeVar) CheckerState a

typecheck :: StaticContext -> Loc ValExpr -> Either (TypeError, TypeVarMap) Type
typecheck staticCtx expr = runReader (evalStateT (runExceptT checker) emptyCheckState) staticCtx
    where
        checker :: Checker Type
        checker = typecheck' emptyContext expr >>= typeRepresentative

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
typecheck' :: Context -> Loc ValExpr -> Checker Type

typecheck' ctx (L _ (VELet bindings body)) = do
    -- Check each let binding and get a list of their constriants, patterns and types,
    -- along with a substitution for all the learned information from checking them
    extensions <- checkLetBindings
    -- Extend the context with the generalised types we inferred
    pushStackFrame
    ctx' <- extendGeneralise ctx extensions
    -- Typecheck the body under the extended context
    bodyType <- typecheck' ctx' body
    -- Check that any relevant variables introduced are now consumed
    checkRelevant
    popStackFrame
    pure bodyType
    where
        checkLetBindings :: Checker [(Multiplicity, Loc Pattern, Type)]
        checkLetBindings = do
            let projectAnnotation (LetBinding _ ann _) = syntax ann
                annotatedPatterns = map (projectAnnotation . syntax) bindings
                patterns = map (\(Annotated pattern _) -> pattern) annotatedPatterns

            -- We create new type variables for each of the annotated patterns
            initialBoundTypes <- mapM annotationToType annotatedPatterns
            pushStackFrame
            -- We extend the context with the new type variables in order to type check the
            -- bound expressions
            --
            -- We always extend with normal multiplicity for recursive function bindings.
            ctx' <- extendNormal ctx (zip3 (repeat $ MAtom Normal) patterns initialBoundTypes)
            -- Next, we map over checking each binding to get a list of the types we inferred
            result <- mapM (checkBinding ctx') (zip (map syntax bindings) initialBoundTypes)
            popStackFrame
            pure result

        checkBinding :: Context -> (LetBinding, Type) -> Checker (Multiplicity, Loc Pattern, Type)
        checkBinding ctx' (binding, initialBoundType) = do
            let (LetBinding m (L _ (Annotated pattern patType)) bound) = binding
            letMul <- annotationToMultiplicity m
            -- We need to tighten the context constraints for the bound expression - these must be 
            -- extended to account for the the fact that the newly bound variable could have a 
            -- weaker multiplicity than one of the values it depends on - this cannot be allowed,
            -- as we could then indirectly violate the multiplicity constraint. So, we tighten
            -- the context to prevent stronger values from being used incorrectly
            pushStackFrame
            boundType <- typecheck' (tighten ctx' letMul) bound
            popStackFrame
            unify (location bound) initialBoundType boundType
            -- Check that if there was an explicit annotation, that the type we inferred unifies with it.
            -- If there was an annotation, and we have inferred a type which proves the annotation is
            -- appropriate, then we should just use the annotation
            checkTypeEntails ctx' boundType patType
            -- Add the constraint pattern type triple for this binding
            pure (letMul, pattern, boundType)

typecheck' ctx (L _ (VECase mul disc branches)) = do
    caseMul <- annotationToMultiplicity mul
    -- Check the discriminator
    -- We need to tighten constraints for the discriminator expression - these are extended to account
    -- for the fact that we will destruct the discriminator `caseM` times - so if `caseM` is
    -- a weaker multiplicity than the current constraint, we must tighten.
    discType <- typecheck' (tighten ctx caseMul) disc

    -- Get the variable constraint sets. These must be folded through the branches to check
    -- how each branch uses them.
    vSets <- gets (^. varFrame)
    -- We also want to fold through a result type for the branches. Initially, we have no idea
    -- what type the branches will result in, so we just create a fresh polymorphic variable.
    -- The idea is that after each branch is typed, we will use the most general unifier between
    -- the current best type, and the type we have just seen for this branch. Then, we will feed
    -- this newly unified type onto the next branch.
    initialBranchType <- freshPolyType
    outVSets <- foldM (compareBranches caseMul discType initialBranchType) vSets branches
    modify (varFrame .~ outVSets)
    typeRepresentative initialBranchType
    where
        compareBranches :: Multiplicity -> Type -> Type -> CheckVarFrame
                        -> Loc CaseBranch
                        -> Checker CheckVarFrame

        compareBranches caseMul discType branchType inVSets branch = do
            -- Then, we actually check the branch. This returns firstly the type we infer from the
            -- branch
            pushVarFrame
            branchType' <- checkBranch caseMul discType (syntax branch)
            branchVSets <- gets (^. varFrame)
            popVarFrame
            -- Now we unify our updated view of the previously expected branch type with the newly
            -- inferred branch type.
            unify (location branch) branchType branchType'

            pure (foldVSets inVSets branchVSets)

        checkBranch :: Multiplicity -> Type -> CaseBranch -> Checker Type
        checkBranch caseMul discType (CaseBranch pattern body) = do
            -- Extend the context with the pattern under the constraint provided by the case statement
            pushStackFrame
            ctx' <- extendNormal ctx [(caseMul, pattern, discType)]
            -- Check the branch itself
            branchType <- typecheck' ctx' body
            -- Check that any relevant variables introduced within the branch itself have been consumed
            checkRelevant
            popStackFrame
            pure branchType

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
        foldVSets :: CheckVarFrame -> CheckVarFrame -> CheckVarFrame
        foldVSets a =   (affineVars %~ S.intersection (a ^. affineVars))
                      . (relevantVars %~ S.intersection (a ^. relevantVars))
                      . (zeroVars %~ S.intersection (a ^. zeroVars))

typecheck' ctx (L _ (VEApp fun arg)) = do
    funType <- typecheck' ctx fun 
    funMul <- unpackFunMul funType
    argType <- typecheck' (tighten ctx funMul) arg

    returnType <- freshPolyType
    unify (location fun) funType (FunctionType argType (Arrow funMul) returnType)
    pure returnType
    where
        unpackFunMul :: Type -> Checker Multiplicity
        unpackFunMul (FunctionType _ (Arrow m) _) = pure m
        unpackFunMul _ = freshPolyMul

typecheck' ctx (L _ (VELambda (L _ ann@(Annotated pattern patType)) (L _ (ArrowExpr arrow)) body)) = do
    argType <- annotationToType ann
    arrowMul <- annotationToMultiplicity arrow
    pushStackFrame
    ctx' <- extendNormal ctx [(arrowMul, pattern, argType)]
    bodyType <- typecheck' ctx' body
    checkTypeEntails ctx argType patType
    checkRelevant
    popStackFrame
    pure (FunctionType argType (Arrow arrowMul) bodyType)

typecheck' ctx (L loc (VEVar x)) = contextLookup ctx loc x

typecheck' ctx (L _ (VELiteral lit)) = typecheckLiteral ctx lit

typecheckLiteral :: Context -> Literal (Loc ValExpr) -> Checker Type
typecheckLiteral _ (IntLiteral _) = pure B.intType

typecheckLiteral _ (RealLiteral _) = pure B.realType

typecheckLiteral ctx (ListLiteral es) = do
    initialListType <- freshPolyType
    mapM_ (unifyElements initialListType) es
    pure (TypeApp B.listTypeCon initialListType)
    where
        unifyElements :: Type -> Loc ValExpr -> Checker ()
        unifyElements t expr = do
            t' <- typecheck' ctx expr
            unify (location expr) t' t

typecheckLiteral ctx (TupleLiteral exprs) = do
    types <- mapM (typecheck' ctx) exprs
    pure (TupleType types)

testEverything :: String -> IO ()
testEverything s = case typecheck B.defaultBuiltins (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (showError s tvm e)
                     Right t -> putStrLn (showType M.empty t)
    where
        fromRight (Right x) = x

