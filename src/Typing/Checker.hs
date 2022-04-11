module Typing.Checker where

import Parser.AST
import Parser.Parser (test_parseExpr)
import Typing.Types
import Typing.Judgement
import qualified Util.Stream as Stream
import qualified Util.BoundedPoset as P

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
import Debug.Trace

-- type RemapperState a = StateT (M.HashMap Identifier TypeVar) CheckerState a

typecheck :: StaticContext -> Loc ValExpr -> Either (TypeError, TypeVarMap) (TypedExpr, MultiplicityPoset)
typecheck staticCtx expr = runReader (evalStateT (runExceptT checker) emptyCheckState) staticCtx
    where
        checker :: Checker (TypedExpr, MultiplicityPoset)
        checker = do
            typed <- typecheck' emptyContext expr >>= remapToReps
            poset <- gets (^. mulRelation)
            pure (typed, poset)

        remapToReps :: TypedExpr -> Checker TypedExpr
        remapToReps (Let t binds body) =
            Let <$> typeRepresentative t <*> mapM remapBind binds <*> remapToReps body
            where
                remapBind :: TypedLetBinding -> Checker TypedLetBinding
                remapBind (TypedLetBinding mul pat bind) = 
                    TypedLetBinding mul <$> remapPattern pat <*> remapToReps bind
        remapToReps (Case t mul disc branches) =
            Case <$> typeRepresentative t <*> pure mul <*> remapToReps disc <*> mapM remapBranch branches
            where
                remapBranch :: TypedCaseBranch -> Checker TypedCaseBranch
                remapBranch (TypedCaseBranch pat expr) =
                    TypedCaseBranch <$> remapPattern pat <*> remapToReps expr
        remapToReps (Application t fun arg) =
            Application <$> typeRepresentative t <*> remapToReps fun <*> remapToReps arg
        remapToReps (Lambda t mul arg body) =
            Lambda <$> typeRepresentative t <*> pure mul <*> remapPattern arg <*> remapToReps body
        remapToReps (Variable t name) =
            Variable <$> typeRepresentative t <*> pure name
        remapToReps (Literal t lit) =
            Literal <$> typeRepresentative t <*> pure lit

        remapPattern :: Pattern -> Checker Pattern
        remapPattern (VariablePattern t name) =
            VariablePattern <$> typeRepresentative t <*> pure name
        remapPattern (ConstructorPattern name ps) =
            ConstructorPattern name <$> mapM remapPattern ps
        remapPattern (LiteralPattern lit) = LiteralPattern <$> remapLitPattern lit
            where
                remapLitPattern :: Literal Pattern -> Checker (Literal Pattern)
                remapLitPattern (IntLiteral i) = pure (IntLiteral i)
                remapLitPattern (RealLiteral r) = pure (RealLiteral r)
                remapLitPattern (ListLiteral ls) = ListLiteral <$> mapM remapPattern ls
                remapLitPattern (TupleLiteral ts) = TupleLiteral <$> mapM remapPattern ts


-- Typecheck and infer the type of an expression under a given variable context.
typecheck' :: Context -> Loc ValExpr -> Checker TypedExpr

typecheck' ctx (L _ (VELet bindings body)) = do
    -- Check each let binding and get a list of their constriants, patterns and types,
    -- along with a substitution for all the learned information from checking them
    extensions <- checkLetBindings
    -- Extend the context with the generalised types we inferred
    pushStackFrame
    (ctx', patterns) <- extendGeneralise ctx (map (fmap typeof) extensions)
    -- Typecheck the body under the extended context
    typedBody <- typecheck' ctx' body
    -- Check that any relevant variables introduced are now consumed
    checkRelevant
    popStackFrame
    pure (Let (typeof typedBody) (reconstructBinders extensions patterns) typedBody)
    where
        checkLetBindings :: Checker [(Multiplicity, Loc SourcePattern, TypedExpr)]
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
            (ctx', _) <- extendNormal ctx (zip3 (repeat $ MAtom Normal) patterns initialBoundTypes)
            -- Next, we map over checking each binding to get a list of the types we inferred
            result <- mapM (checkBinding ctx') (zip (map syntax bindings) initialBoundTypes)
            popStackFrame
            pure result

        checkBinding :: Context -> (LetBinding, Type) -> Checker (Multiplicity, Loc SourcePattern, TypedExpr)
        checkBinding ctx' (binding, initialBoundType) = do
            let (LetBinding m (L _ (Annotated pattern patType)) bound) = binding
            letMul <- annotationToMultiplicity m
            -- We need to tighten the context constraints for the bound expression - these must be 
            -- extended to account for the the fact that the newly bound variable could have a 
            -- weaker multiplicity than one of the values it depends on - this cannot be allowed,
            -- as we could then indirectly violate the multiplicity constraint. So, we tighten
            -- the context to prevent stronger values from being used incorrectly
            pushStackFrame
            typedBinder <- typecheck' (tighten ctx' letMul) bound
            popStackFrame
            unify (location bound) initialBoundType (typeof typedBinder)
            -- Check that if there was an explicit annotation, that the type we inferred unifies with it.
            -- If there was an annotation, and we have inferred a type which proves the annotation is
            -- appropriate, then we should just use the annotation
            checkTypeEntails ctx' (typeof typedBinder) patType
            -- Add the constraint pattern type triple for this binding
            pure (letMul, pattern, typedBinder)

        reconstructBinders :: [(Multiplicity, Loc SourcePattern, TypedExpr)] -> [Pattern] -> [TypedLetBinding]
        reconstructBinders [] [] = []
        reconstructBinders ((mul, _, expr):exprs) (pat:pats) =
            TypedLetBinding mul pat expr : reconstructBinders exprs pats

typecheck' ctx (L _ (VECase mul disc branches)) = do
    caseMul <- annotationToMultiplicity mul
    -- Check the discriminator
    -- We need to tighten constraints for the discriminator expression - these are extended to account
    -- for the fact that we will destruct the discriminator `caseM` times - so if `caseM` is
    -- a weaker multiplicity than the current constraint, we must tighten.
    typedDisc <- typecheck' (tighten ctx caseMul) disc

    -- Get the variable constraint sets. These must be folded through the branches to check
    -- how each branch uses them.
    vSets <- gets (^. varFrame)
    -- We also want to fold through a result type for the branches. Initially, we have no idea
    -- what type the branches will result in, so we just create a fresh polymorphic variable.
    -- The idea is that after each branch is typed, we will use the most general unifier between
    -- the current best type, and the type we have just seen for this branch. Then, we will feed
    -- this newly unified type onto the next branch.
    initialBranchType <- freshPolyType
    (branchVSets, branches) <- NE.unzip <$> mapM (compareBranches caseMul (typeof typedDisc) initialBranchType) branches
    modify (varFrame .~ foldl foldVSets vSets branchVSets)
    branchType <- typeRepresentative initialBranchType
    pure (Case branchType caseMul typedDisc branches)
    where
        compareBranches :: Multiplicity -> Type -> Type
                        -> Loc CaseBranch
                        -> Checker (CheckVarFrame, TypedCaseBranch)

        compareBranches caseMul discType branchType branch = do
            -- Then, we actually check the branch. This returns firstly the type we infer from the
            -- branch
            pushVarFrame
            typedBranch <- checkBranch caseMul discType (syntax branch)
            branchVSets <- gets (^. varFrame)
            popVarFrame
            -- Now we unify our updated view of the previously expected branch type with the newly
            -- inferred branch type.
            unifyLUB True (location branch) branchType (typeof typedBranch)

            pure (branchVSets, typedBranch)

        checkBranch :: Multiplicity -> Type -> CaseBranch -> Checker TypedCaseBranch
        checkBranch caseMul discType (CaseBranch pattern body) = do
            -- Extend the context with the pattern under the constraint provided by the case statement
            pushStackFrame
            (ctx', pats) <- extendNormal ctx [(caseMul, pattern, discType)]
            let [pat] = pats
            -- Check the branch itself
            typedBranch <- typecheck' ctx' body
            -- Check that any relevant variables introduced within the branch itself have been consumed
            checkRelevant
            popStackFrame
            pure (TypedCaseBranch pat typedBranch)

        -- takeBounds :: Type -> Type -> Checker ()
        -- takeBounds 

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
    typedFun <- typecheck' ctx fun 
    funMul <- unpackFunMul (typeof typedFun)
    typedArg <- typecheck' (tighten ctx funMul) arg

    returnType <- freshPolyType
    unify (location fun) (typeof typedFun) (FunctionType (typeof typedArg) (Arrow funMul) returnType)
    retTypeRep <- typeRepresentative returnType
    pure (Application retTypeRep typedFun typedArg)
    where
        unpackFunMul :: Type -> Checker Multiplicity
        unpackFunMul (FunctionType _ (Arrow m) _) = pure m
        unpackFunMul _ = pure (MAtom Normal)

typecheck' ctx (L _ (VELambda (L _ ann@(Annotated pattern patType)) (L _ (ArrowExpr arrow)) body)) = do
    argType <- annotationToType ann
    arrowMul <- annotationToMultiplicity arrow
    pushStackFrame
    (ctx', pats) <- extendNormal ctx [(arrowMul, pattern, argType)]
    let [pat] = pats
    typedBody <- typecheck' ctx' body
    checkTypeEntails ctx argType patType
    checkRelevant
    popStackFrame
    pure (Lambda (FunctionType argType (Arrow arrowMul) (typeof typedBody)) arrowMul pat typedBody)

typecheck' ctx (L loc (VEVar x)) = Variable <$> contextLookup ctx loc x <*> pure x

typecheck' ctx (L _ (VELiteral lit)) = typecheckLiteral ctx lit

typecheckLiteral :: Context -> Literal (Loc ValExpr) -> Checker TypedExpr
typecheckLiteral _ (IntLiteral i) = pure (Literal B.intType (IntLiteral i))

typecheckLiteral _ (RealLiteral r) = pure (Literal B.realType (RealLiteral r))

typecheckLiteral ctx (ListLiteral es) = do
    initialListType <- freshPolyType
    Literal (TypeApp B.listTypeCon initialListType) . ListLiteral <$> mapM (unifyElements initialListType) es
    where
        unifyElements :: Type -> Loc ValExpr -> Checker TypedExpr
        unifyElements t expr = do
            t' <- typecheck' ctx expr
            unify (location expr) (typeof t') t
            pure t'

typecheckLiteral ctx (TupleLiteral exprs) = do
    typedExprs <- mapM (typecheck' ctx) exprs
    pure (Literal (TupleType (map typeof typedExprs)) (TupleLiteral typedExprs))

testEverything :: String -> IO ()
testEverything s = case typecheck B.defaultBuiltins (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (showError s tvm e)
                     Right (t, _) -> putStrLn (showType M.empty (typeof t))
    where
        fromRight (Right x) = x

testTypeCheck :: String -> IO ()
testTypeCheck s = case typecheck B.defaultBuiltins (fromRight (test_parseExpr s)) of
                     Left (e, tvm) -> putStrLn (showError s tvm e)
                     Right (t, _) -> print t
    where
        fromRight (Right x) = x

