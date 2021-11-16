{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module Typing.Types 
    ( TypeError(..)
    , VarSet
    , TypeVar
    , MultiplicityVar
    , SubMap
    , TypeVarMap
    , Type(..)
    , Arrow(..)
    , CheckState(..), affineVars, relevantVars, zeroVars, freshTypeVars, varAssignments
    , CheckerState
    , Checker
    , TypeScheme(..), quantifiedTVars, baseType
    , MultiplicityScheme, quantifiedMVars, baseMul
    , MConstraint(..)
    , Context(..), termContext, mulContext, typeNameContext
    , StaticContext(..), defaultFunctions, dataConstructors, dataTypes
    , Typed(..)

    , emptyContext
    , emptyCheckState
    , emptySub

    , typeError
    , showError

    , intType, realType, unitType, boolType, listTypeCon
    ) where

import Parser.AST
    ( Identifier(..)
    , Multiplicity(..)
    , SourceLocation(..)
    )

import qualified Util.Stream as Stream

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (intercalate)

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding (Context)

type Message = String

data TypeError
    = RelevancyViolation SourceLocation Identifier
    | AffinityViolation SourceLocation Identifier
    | ContextRelevancyViolation SourceLocation Identifier
    | ContextAffinityViolation SourceLocation Identifier
    | VariableNotInScope SourceLocation Identifier
    | ConstructorNotInScope SourceLocation Identifier
    | IncompletePattern SourceLocation Identifier
    | TooManyArguments SourceLocation Identifier
    | GroundUnificationFailure SourceLocation Identifier Identifier
    | UnificationFailure SourceLocation Type Type
    | OccursCheckFailure SourceLocation TypeVar Type
    | EntailmentFailure SourceLocation Type
    | GenericError (Maybe SourceLocation) Message
    | TypeErrorList [TypeError]

type VarSet = S.HashSet Identifier
type TypeVar = Integer
type MultiplicityVar = String
type SubMap = M.HashMap TypeVar Type
type TypeVarMap = M.HashMap TypeVar Identifier

data Type
    = Ground Identifier
    | Poly TypeVar
    | TypeApp Type Type
    -- TODO: This maybe shouldn't use a syntactic arrow, but instead a logical one?
    | FunctionType Type Arrow Type
    | TupleType [Type]
    deriving (Eq, Show)

newtype Arrow = Arrow (Maybe Multiplicity)
    deriving (Eq, Show)

data CheckState = CheckState
    { _affineVars       :: VarSet
    , _relevantVars     :: VarSet
    , _zeroVars         :: VarSet
    , _freshTypeVars    :: Stream.Stream TypeVar
    , _varAssignments   :: TypeVarMap
    }

makeLenses ''CheckState

class Typed a where
    ftv :: a -> S.HashSet TypeVar
    substitute :: SubMap -> a -> a

instance Typed a => Typed [a] where
    ftv = S.unions . (ftv <$>)
    substitute s = (substitute s <$>)

instance Typed Type where
    ftv (Ground {}) = S.empty
    ftv (Poly p) = S.singleton p
    ftv (TypeApp fun arg) = ftv fun `S.union` ftv arg
    ftv (FunctionType from _ to) = ftv from `S.union` ftv to
    ftv (TupleType ts) = ftv ts

    substitute _ ty@(Ground {}) = ty
    substitute s ty@(Poly name) = M.lookupDefault ty name s
    substitute s (TypeApp fun arg) = TypeApp (substitute s fun) (substitute s arg)
    substitute s (FunctionType from arrow to) = FunctionType (substitute s from) arrow (substitute s to)
    substitute s (TupleType ts) = TupleType (substitute s ts)

data TypeScheme = TypeScheme
    { _quantifiedTVars :: [TypeVar]
    , _baseType :: Type
    }
    deriving Show

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
    , _typeNameContext :: M.HashMap Identifier TypeVar
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
    ftv (Context termCtx _ _) = ftv (fst <$> M.elems termCtx)
    substitute s = termContext %~ M.map substituteElement
        where
            substituteElement :: (TypeScheme, MConstraint) -> (TypeScheme, MConstraint)
            substituteElement (scheme, constraint) = (substitute s scheme, constraint)

emptyContext :: Context
emptyContext = Context M.empty M.empty M.empty

emptyCheckState :: CheckState
emptyCheckState = CheckState S.empty S.empty S.empty (Stream.iterate (+ 1) 0) M.empty

emptySub :: SubMap
emptySub = M.empty

typeError :: TypeError -> Checker a
typeError err = do
    varMap <- gets (^. varAssignments)
    throwError (err, varMap)

intType, realType, unitType, boolType, listTypeCon :: Type
intType = Ground (I "Int")
realType = Ground (I "Real")
unitType = Ground (I "()")
boolType = Ground (I "Bool")
listTypeCon = Ground (I "[]")

showError :: String -> TypeVarMap -> TypeError -> String
showError text tvm (RelevancyViolation loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" was marked relevant, but never consumed."
showError text tvm (AffinityViolation loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" was marked affine, but consumed more than once."
showError text tvm (ContextRelevancyViolation loc name) =
    showContext text loc ++ "Variable \"" ++ show name ++ "\" with relevant constraint used in a context which may violate relevancy."
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
showError text tvm (EntailmentFailure loc t) =
    showContext text loc ++ "Type \"" ++ showType tvm t ++ "\" does not entail the annotated type."
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

showContext :: String -> SourceLocation -> String
showContext text loc = intercalate "\n" (findLines (slStart loc) (slEnd loc) lengthLines) ++ "\n" ++ show loc
    where
        lengthLines :: [(Int, String)]
        lengthLines = map (\line -> (length line + 1, line)) (lines text)

        findLines :: Int -> Int -> [(Int, String)] -> [String]
        findLines _ _ [] = []
        findLines start end ((size, line):lines)
            | start' < 0 && end >= 0 = line : highlightLine : findLines start' end' lines
            | end < 0 = []
            | otherwise = findLines start' end' lines
            where
                start', end' :: Int
                start' = start - size
                end' = end - size

                highlightLine = replicate start ' ' ++ replicate (min end (size - 1) - max 0 start) '^'

