{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module Typing.Judgement where

import Parser.Parser (Identifier, Pattern(..), Multiplicity(..), MultiplicityAtom(..), TypeExpr(..))
import qualified Util.Stream as Stream

import Control.Monad.Except
import Control.Monad.State
import Control.Lens hiding (Context)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Maybe (isJust)

type VarSet = S.HashSet Identifier
type TypeVar = Integer
type MultiplicityVar = String
type SubMap = M.HashMap TypeVar (TypeExpr TypeVar)

data CheckState = CheckState
    { _affineVars       :: VarSet
    , _relevantVars     :: VarSet
    , _zeroVars         :: VarSet
    , _freshTypeVars    :: Stream.Stream TypeVar
    }

makeLenses ''CheckState

type CheckerState = State CheckState
type Checker a = ExceptT String CheckerState a

class Typed a where
    ftv :: a -> S.HashSet TypeVar
    substitute :: SubMap -> a -> a

instance Typed a => Typed [a] where
    ftv = S.unions . (ftv <$>)
    substitute s = (substitute s <$>)

instance Typed (TypeExpr TypeVar) where
    ftv (TEGround _) = S.empty
    ftv (TEPoly p) = S.singleton p
    ftv (TEApp fun arg) = ftv fun `S.union` ftv arg
    ftv (TEArrow from _ to) = ftv from `S.union` ftv to
    ftv TEUnit = S.empty
    ftv (TETuple ts) = ftv ts
    ftv (TEList t) = ftv t

    substitute s ty@(TEPoly name) = M.lookupDefault ty name s
    substitute s (TEApp fun arg) = TEApp (substitute s fun) (substitute s arg)
    substitute s (TEArrow from arrow to) = TEArrow (substitute s from) arrow (substitute s to)
    substitute s (TETuple ts) = TETuple (substitute s ts)
    substitute s (TEList t) = TEList (substitute s t)
    substitute _ ty = ty

data TypeScheme = TypeScheme
    { _quantifiedTVars :: [TypeVar]
    , _baseType :: TypeExpr TypeVar
    }

makeLenses ''TypeScheme

instance Typed TypeScheme where
    ftv (TypeScheme vars t) = S.difference (ftv t) (S.fromList vars)
    substitute s (TypeScheme vars t) = TypeScheme vars (substitute (withoutKeys s $ S.fromList vars) t)
        where
            withoutKeys m toDrop = M.filterWithKey (\k _ -> not (k `S.member` toDrop)) m

data MultiplicityScheme = MultiplicityScheme
    { _quantifiedMVars :: [MultiplicityVar]
    , _baseMul :: Multiplicity
    }

makeLenses ''MultiplicityScheme

data MConstraint = MConstraint Bool Bool

data Context = Context 
    { _termContext :: M.HashMap Identifier (TypeScheme, MConstraint)
    , _mulContext :: M.HashMap Identifier MultiplicityScheme
    }

makeLenses ''Context

instance Typed Context where
    ftv (Context termCtx _) = ftv (fst <$> M.elems termCtx)
    substitute s = termContext %~ M.map substituteElement
        where
            substituteElement :: (TypeScheme, MConstraint) -> (TypeScheme, MConstraint)
            substituteElement (scheme, constraint) = (substitute s scheme, constraint)

emptyContext :: Context
emptyContext = Context M.empty M.empty

emptyCheckState :: CheckState
emptyCheckState = CheckState S.empty S.empty S.empty (Stream.iterate (+ 1) 0)

emptySub :: SubMap
emptySub = M.empty

constraintFor :: MultiplicityAtom -> MConstraint
constraintFor Normal = MConstraint False False
constraintFor Linear = MConstraint True True
constraintFor Relevant = MConstraint False True
constraintFor Affine = MConstraint True False

extend :: Bool -> Context -> MConstraint -> Pattern -> TypeExpr TypeVar -> Checker (Context, SubMap, Checker ())
extend generaliseTypes context mul@(MConstraint affine relevant) pattern typeExpr = do
    relevantSet <- lift $ gets (^. relevantVars)
    (ctx, sub) <- extend' context pattern typeExpr
    pure (ctx, sub, createRelevantChecker relevantSet)
    where
        extend' :: Context -> Pattern -> TypeExpr TypeVar -> Checker (Context, SubMap)
        extend' ctx (VarPattern name) t = do
            when affine $ modify (affineVars %~ S.insert name)
            when relevant $ modify (relevantVars %~ S.insert name)
            let ctx' = (termContext %~ M.insert name (generalise ctx t, mul)) ctx
            pure (ctx', emptySub)
        extend' _ _ _ = throwError "Non variable patterns not yet supported."

        createRelevantChecker :: VarSet -> Checker ()
        createRelevantChecker before = do
            after <- lift $ gets (^. relevantVars)
            let remaining = after `S.difference` before
            unless (S.null remaining) $ 
                throwError $ "Variable(s) '" ++ show (S.toList remaining) ++ "' were marked as relevant, but never consumed."

        generalise :: Context -> TypeExpr TypeVar -> TypeScheme
        generalise ctx t 
            | generaliseTypes = TypeScheme (S.toList (S.difference (ftv t) (ftv ctx))) t
            | otherwise = TypeScheme [] t

tighten :: Context -> MConstraint -> Context
tighten ctx constraint = (termContext %~ M.map tightenElem) ctx
    where
        tightenElem :: (TypeScheme, MConstraint) -> (TypeScheme, MConstraint)
        tightenElem (scheme, vConstraint) = (scheme, vConstraint %/ constraint)

contextLookup :: Context -> Identifier -> Checker (TypeExpr TypeVar)
contextLookup ctx name = case M.lookup name (ctx ^. termContext) of
                           Nothing -> throwError ("Variable '" ++ name ++ "' missing in context.")
                           Just (scheme, constraint) -> do
                               checkAndConsume constraint
                               instantiate scheme
    where
        checkAndConsume :: MConstraint -> Checker ()
        checkAndConsume (MConstraint allowedAffine allowedRelevant) = do
            -- If the variable we are trying to use is in the zero set, it cannot be consumed.
            isZeroed <- checkInSet zeroVars
            when isZeroed $ throwError $ "Variable '" ++ name ++ "' with affine constraint already used."
            -- If the variable is affine constrained, but affine variables cannot be used in the constraint
            -- context, then throw
            isAffine <- checkInSet affineVars
            when (isAffine && not allowedAffine) $ throwError $
                "Variable '" ++ name ++ "' with affine constraint used in context which may violate affinity."
            -- If the variable is relevant, but relevant variables cannot be used, then throw
            isRelevant <- checkInSet relevantVars
            when (isRelevant && not allowedRelevant) $ throwError $
                "Variable '" ++ name ++ "' with relevant constraint used in context which may violate relevenancy."

            -- Now we consume the variable, as it has passed the checks
            -- We actually don't logically need to check for the deletions if they are in
            -- the set. However, if we already know they are not, it is more efficient
            -- to just not run the delete method.
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

        instantiate :: TypeScheme -> Checker (TypeExpr TypeVar)
        instantiate (TypeScheme vars t) = do
            freshVars <- mapM (const $ TEPoly <$> lift freshVar) vars
            pure $ substitute (M.fromList (zip vars freshVars)) t

freshVar :: CheckerState TypeVar
freshVar = do
    (var Stream.:> rest) <- gets (^. freshTypeVars)
    modify (freshTypeVars .~ rest)
    pure var

infixl 7 %/
(%/) :: MConstraint -> MConstraint -> MConstraint
(MConstraint a r) %/ (MConstraint a' r') = MConstraint (a && a') (r && r')

infixl 5 +.
(+.) :: SubMap -> SubMap -> SubMap
s1 +. s0 = M.map (substitute s1) s0 <> s1

