{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveGeneric, MultiParamTypeClasses #-}
module Typing.Types 
    ( TypeError(..)
    , VarSet
    , TermVar
    , TypeVar
    , MultiplicityVar , TypeVarMap
    , MultiplicityPoset
    , Type(..)
    , Multiplicity(..)
    , Arrow(..)
    , TypedExpr(..)
    , TypedCaseBranch(..)
    , TypedLetBinding(..)
    , Pattern(..)
    , typeof

    , CheckStackFrame(..)
    , termNameContext
    , addedTermNames
    , typeNameContext
    , mulNameContext

    , CheckVarFrame(..)
    , affineVars
    , relevantVars
    , zeroVars

    , CheckState(..)
    , stackFrame
    , varFrame 
    , freshTermVars
    , freshTypeVars
    , typeEquivalences
    , freshMulVars
    , mulEquivalences
    , mulRelation
    , termVarAssignments
    , typeVarAssignments
    , mulVarAssignments

    , pushStackFrame
    , popStackFrame
    , pushVarFrame
    , popVarFrame

    , CheckerState
    , Checker
    , TypeScheme(..), quantifiedTVars, quantifiedMVars, baseType
    , Context(..), termContext
    , StaticContext(..), defaultFunctions, dataConstructors, dataTypes
    , Typed(..)

    , emptyContext
    , emptyCheckState

    , typeError
    , showError, showType
    ) where

import Parser.AST
    ( Identifier(..)
    , SourceLocation(..)
    , Loc(..)
    , SourcePattern(..)
    , MultiplicityAtom(..)
    , Literal(..)
    )

import qualified Util.Stream as Stream
import qualified Util.BoundedPoset as P
import Error.Error (showContext)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.DisjointSet as DS
import Data.List (intercalate)
import qualified Data.List.NonEmpty as NE

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Context)

import GHC.Generics (Generic)
import Data.Hashable (Hashable)

type Message = String

data TypeError
    = RelevancyViolation SourceLocation Identifier
    | AffinityViolation SourceLocation Identifier
    | ContextAffinityViolation SourceLocation Identifier
    | DuplicateVariableDefinition SourceLocation Identifier
    | VariableNotInScope SourceLocation Identifier
    | ConstructorNotInScope SourceLocation Identifier
    | IncompletePattern SourceLocation Identifier
    | TooManyArguments SourceLocation Identifier
    | GroundUnificationFailure SourceLocation Identifier Identifier
    | UnificationFailure SourceLocation Type Type
    | OccursCheckFailure SourceLocation TypeVar Type
    | MAtomUnificationFailure SourceLocation MultiplicityAtom MultiplicityAtom
    | MOrderingViolation SourceLocation Multiplicity Multiplicity
    | EntailmentFailure SourceLocation Type
    | EntailmentMultiAssign SourceLocation TypeVar
    | GenericError (Maybe SourceLocation) Message
    | TypeErrorList [TypeError]

type VarSet = S.HashSet TermVar
type TermVar = Integer
type TypeVar = Integer
type MultiplicityVar = Integer
type TypeVarMap = M.HashMap TypeVar Identifier

type MultiplicityPoset = P.BoundedPoset MultiplicityAtom Multiplicity

data Type
    = Poly TypeVar
    | Ground Identifier
    | TypeApp Type Type
    | FunctionType Type Arrow Type
    | TupleType [Type]
    deriving (Eq, Ord, Show)

data Multiplicity
    = MPoly MultiplicityVar
    | MProd Multiplicity Multiplicity
    | MAtom MultiplicityAtom
    deriving (Eq, Ord, Generic)

instance Show Multiplicity where
    show (MPoly var) = show var
    show (MProd lhs rhs) = show lhs ++ " * " ++ show rhs
    show (MAtom atom) = show atom

instance Hashable Multiplicity

instance P.FixedCorePoset MultiplicityAtom Multiplicity where
    Linear <=? _ = True
    _ <=? Normal = True
    a <=? b = a == b
    bottom = Linear
    top = Normal
    lub Relevant Affine = Normal
    lub Affine Relevant = Normal
    lub a b
        | a P.<=? b = b
        | otherwise = a
    glb Relevant Affine = Linear
    glb Affine Relevant = Linear
    glb a b
        | a P.<=? b = a
        | otherwise = b
    unembed (MAtom a) = Just a
    unembed _ = Nothing
    unconj (MProd l r) = Just (l, r)
    unconj _ = Nothing

newtype Arrow = Arrow Multiplicity
    deriving (Eq, Ord)

instance Show Arrow where
    show (Arrow (MAtom Normal)) = "->"
    show (Arrow (MAtom Linear)) = "-o"
    show (Arrow m) = "-> " ++ show m

class TypeContainer a where
    typeof :: a -> Type

data TypedExpr
    = Let Type [TypedLetBinding] TypedExpr
    | Case Type Multiplicity TypedExpr (NE.NonEmpty TypedCaseBranch)
    | Application Type TypedExpr TypedExpr
    | Lambda Type Multiplicity Pattern TypedExpr
    | Variable Type Identifier
    | Literal Type (Literal TypedExpr)
    deriving Show
    
instance TypeContainer TypedExpr where
    typeof (Let t _ _) = t
    typeof (Case t _ _ _) = t
    typeof (Application t _ _) = t
    typeof (Lambda t _ _ _) = t
    typeof (Variable t _) = t
    typeof (Literal t _) = t

data TypedLetBinding = TypedLetBinding Multiplicity Pattern TypedExpr
    deriving Show

instance TypeContainer TypedLetBinding where
    typeof (TypedLetBinding _ _ e) = typeof e

data TypedCaseBranch = TypedCaseBranch Pattern TypedExpr
    deriving Show

instance TypeContainer TypedCaseBranch where
    typeof (TypedCaseBranch _ e) = typeof e

data Pattern
    = VariablePattern Type Identifier
    | ConstructorPattern Identifier [Pattern]
    | LiteralPattern (Literal Pattern)
    deriving Show

data CheckStackFrame = CheckStackFrame
    { _termNameContext :: M.HashMap Identifier TermVar
    , _addedTermNames :: S.HashSet (Loc Identifier)
    , _typeNameContext :: M.HashMap Identifier Type
    , _mulNameContext :: M.HashMap Identifier Multiplicity
    }

makeLenses ''CheckStackFrame

data CheckVarFrame = CheckVarFrame
    { _affineVars           :: VarSet
    , _relevantVars         :: VarSet
    , _zeroVars             :: VarSet
    }

makeLenses ''CheckVarFrame

data CheckState = CheckState
    { _stackFrame           :: CheckStackFrame
    , _checkStack           :: [CheckStackFrame]

    , _varFrame             :: CheckVarFrame
    , _varStack             :: [CheckVarFrame]

    , _freshTermVars        :: Stream.Stream TermVar

    , _freshTypeVars        :: Stream.Stream TypeVar
    , _typeEquivalences     :: DS.DisjointSet Type

    , _freshMulVars         :: Stream.Stream MultiplicityVar
    , _mulEquivalences      :: DS.DisjointSet Multiplicity
    , _mulRelation          :: MultiplicityPoset

    , _termVarAssignments   :: M.HashMap TermVar Identifier
    , _typeVarAssignments   :: TypeVarMap
    , _mulVarAssignments    :: M.HashMap MultiplicityVar Identifier
    }

makeLenses ''CheckState

class Typed a where
    ftv :: a -> S.HashSet TypeVar
    fuv :: a -> S.HashSet MultiplicityVar

instance Typed a => Typed [a] where
    ftv = S.unions . (ftv <$>)
    fuv = S.unions . (fuv <$>)

instance Typed Type where
    ftv (Ground {}) = S.empty
    ftv (Poly p) = S.singleton p
    ftv (TypeApp fun arg) = ftv fun `S.union` ftv arg
    ftv (FunctionType from _ to) = ftv from `S.union` ftv to
    ftv (TupleType ts) = ftv ts

    fuv (TypeApp fun arg) = fuv fun `S.union` fuv arg
    fuv (FunctionType from (Arrow m) to) = fuv m `S.union` fuv from `S.union` fuv to
    fuv (TupleType ts) = fuv ts
    fuv _ = S.empty

instance Typed Multiplicity where
    ftv _ = S.empty

    fuv (MPoly p) = S.singleton p
    fuv (MAtom {}) = S.empty
    fuv (MProd lhs rhs) = fuv lhs `S.union` fuv rhs

data TypeScheme = TypeScheme
    { _quantifiedTVars :: S.HashSet TypeVar
    , _quantifiedMVars :: S.HashSet MultiplicityVar
    , _baseType :: Type
    }

makeLenses ''TypeScheme

instance Typed TypeScheme where
    ftv (TypeScheme vars _ t) = S.difference (ftv t) vars
    fuv (TypeScheme _ mvars t) = S.difference (fuv t) mvars

instance Show TypeScheme where
    show (TypeScheme vars mvars base) =
        "forall " ++
        unwords (S.toList (S.map show vars) <> S.toList (S.map show mvars)) ++
        ". " ++ show base

newtype Context = Context 
    { _termContext :: M.HashMap Identifier (TypeScheme, Multiplicity)
    }

makeLenses ''Context

data StaticContext = StaticContext
    { _defaultFunctions :: M.HashMap Identifier TypeScheme
    , _dataConstructors :: M.HashMap Identifier TypeScheme
    , _dataTypes :: S.HashSet Identifier
    }

makeLenses ''StaticContext

type CheckerState = StateT CheckState (Reader StaticContext)
type Checker a = ExceptT (TypeError, TypeVarMap) CheckerState a

instance Typed Context where
    ftv (Context termCtx) = ftv (fst <$> M.elems termCtx)
    fuv (Context termCtx) = fuv (fst <$> M.elems termCtx)

emptyContext :: Context
emptyContext = Context
    { _termContext = M.empty
    }

emptyCheckState :: CheckState
emptyCheckState = CheckState 
    { _stackFrame = emptyStackFrame
    , _checkStack = []
    , _varFrame = emptyVarFrame
    , _varStack = []
    , _freshTermVars = Stream.iterate (+ 1) 0
    , _freshTypeVars = Stream.iterate (+ 1) 0
    , _freshMulVars = Stream.iterate (+ 1) 0
    , _mulEquivalences = DS.empty
    , _mulRelation = P.empty
    , _typeEquivalences = DS.empty
    , _termVarAssignments = M.empty
    , _mulVarAssignments = M.empty
    , _typeVarAssignments = M.empty
    }

emptyStackFrame :: CheckStackFrame
emptyStackFrame = CheckStackFrame
    { _termNameContext = M.empty
    , _addedTermNames = S.empty
    , _typeNameContext = M.empty
    , _mulNameContext = M.empty
    }

emptyVarFrame :: CheckVarFrame
emptyVarFrame = CheckVarFrame
    { _affineVars = S.empty
    , _relevantVars = S.empty
    , _zeroVars = S.empty
    }

pushStackFrame :: Checker ()
pushStackFrame = do
    top <- gets (^. stackFrame)
    modify ( (checkStack %~ (top:))
           . (stackFrame .~ (addedTermNames .~ S.empty) top))

popStackFrame :: Checker ()
popStackFrame = do
    stack <- gets (^. checkStack)
    case stack of
      -- This case should never happen
      [] -> pure ()
      (top:rest) -> modify ( (checkStack .~ rest)
                           . (stackFrame .~ top))

pushVarFrame :: Checker ()
pushVarFrame = do
    top <- gets (^. varFrame)
    modify (varStack %~ (top:))

popVarFrame :: Checker ()
popVarFrame = do
    stack <- gets (^. varStack)
    case stack of
      [] -> pure ()
      (top:rest) -> modify ( (varStack .~ rest)
                           . (varFrame .~ top))

typeError :: TypeError -> Checker a
typeError err = do
    varMap <- gets (^. typeVarAssignments)
    throwError (err, varMap)

showError :: String -> TypeVarMap -> TypeError -> String
showError text tvm (RelevancyViolation loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" was marked relevant, but might never be consumed."
showError text tvm (AffinityViolation loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" was marked affine, but consumed more than once."
showError text tvm (ContextAffinityViolation loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" with affine constraint used in a context which may violate affinity."
showError text tvm (VariableNotInScope loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" not in scope."
showError text tvm (ConstructorNotInScope loc name) =
    showContext text loc ++ "Data constructor \"" ++ show name ++ "\" not in scope."
showError text tvm (IncompletePattern loc name) =
    showContext text loc ++ "Data constructor \"" ++ show name ++ "\" has an incomplete pattern."
showError text tvm (TooManyArguments loc name) =
    showContext text loc ++ "Data constructor \"" ++ show name ++ "\" given too many arguments."
showError text tvm (GroundUnificationFailure loc name name') =
    showContext text loc ++ "Unification of ground types \"" ++ show name ++ " ~ " ++ show name' ++ "\" failed."
showError text tvm (UnificationFailure loc t t') =
    showContext text loc ++ "Unification of types \"" ++ showType tvm t ++ " ~ " ++ showType tvm t' ++ "\" failed."
showError text tvm (OccursCheckFailure loc tv t) =
    showContext text loc ++ "Occurs check in unification \"" ++ varName ++ " ~ " ++ showType tvm t ++ "\" failed."
    where
        varName :: String
        varName = case M.lookup tv tvm of
                    Nothing -> "<!!!not found!!!>"
                    Just (I name) -> name
showError text tvm (MAtomUnificationFailure loc a a') =
    showContext text loc ++ "Multiplicity atoms could not be unified in \"" ++ show a ++ " ~ " ++ show a' ++ "\"."
showError text tvm (MOrderingViolation loc m m') =
    showContext text loc ++ "Failed to add \"" ++ show m ++ " <= " ++ show m' ++ "\" to contraint graph."
showError text tvm (EntailmentFailure loc t) =
    showContext text loc ++ "Inferred type cannot entail annotated type \"" ++ showType tvm t ++ "\"."
showError text tvm (EntailmentMultiAssign loc tv) =
    showContext text loc ++ "Type variable '" ++ show tv ++ "' was assigned to multiple types in entailment."
showError _ _ (GenericError Nothing message) =
    "<no location>: " ++ message
showError text _ (GenericError (Just loc) message) =
    showContext text loc ++ message
showError text tvm (TypeErrorList errors) =
    intercalate "\n----\n" (map (showError text tvm) errors)

showType :: TypeVarMap -> Type -> String
showType tvm (Ground (I name)) = name
showType tvm (Poly tv) = case M.lookup tv tvm of
                           Nothing -> show tv -- "<!!!not found!!!>"
                           Just (I name) -> name
showType tvm (TypeApp (Ground listType) arg)
    | listType == I "[]" = "[" ++ showType tvm arg ++ "]"
showType tvm (TypeApp con arg) = showType tvm con ++ " " ++ argString arg
    where
        argString :: Type -> String
        argString (TypeApp {}) = "(" ++ showType tvm arg ++ ")"
        argString (FunctionType {}) = "(" ++ showType tvm arg ++ ")"
        argString _ = showType tvm arg
showType tvm (FunctionType from arrow to) = fromString from ++ " " ++ show arrow ++ " " ++ showType tvm to
    where
        fromString :: Type -> String
        fromString (FunctionType {}) = "(" ++ showType tvm from ++ ")"
        fromString _ = showType tvm from
showType tvm (TupleType ts) = "(" ++ intercalate ", " (map (showType tvm) ts) ++ ")"

