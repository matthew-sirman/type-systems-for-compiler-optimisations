{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveGeneric, MultiParamTypeClasses, PatternSynonyms, UndecidableInstances #-}
module Typing.Types where

-- Types used in the type checker modules

import Parser.AST

import qualified Util.Stream as Stream
import qualified Util.ConstrainedPoset as P
import Error.Error (showContext)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.DisjointSet as DS
import qualified Data.DisjointMap as DM
import Data.List (intercalate, intersperse)
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor (bimap, first, second)
import Data.Fix
import Data.Functor.Classes (Show1(..))

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
    | MissingType SourceLocation Identifier
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

type MultiplicityPoset = P.ConstrainedPoset MultiplicityAtom Multiplicity

data Type
    = Poly TypeVar
    | Ground Identifier
    | TypeApp Type Type
    | FunctionType Type Arrow Type
    | TupleType [Type]
    deriving (Eq, Ord)

instance Show Type where
    show (Poly tv) = "'" ++ show tv
    show (Ground name) = show name
    show (TypeApp fun arg) = "(" ++ show fun ++ " " ++ show arg ++ ")"
    show (FunctionType from arrow to) = "(" ++ show from ++ " " ++ show arrow ++ " " ++ show to ++ ")"
    show (TupleType ts) = "(" ++ intercalate ", " (map show ts) ++ ")"

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

data MultiplicityOperation
    = Done Multiplicity
    | LUB Multiplicity
    | GLB Multiplicity

newtype Arrow = Arrow Multiplicity
    deriving (Eq, Ord)

instance Show Arrow where
    show (Arrow (MAtom Normal)) = "->"
    show (Arrow (MAtom Linear)) = "-o"
    show (Arrow m) = "-> " ++ show m

data PrimitiveLiteral
    = IntLit Int
    | RealLit Double

instance Show PrimitiveLiteral where
    show (IntLit i) = show i
    show (RealLit r) = show r

class TypeContainer a where
    typeof :: a -> Type

instance TypeContainer (f (Fix f)) => TypeContainer (Fix f) where
    typeof (Fix t) = typeof t

data TypedExprF t
    = Let_ Type [TypedLetBindingF t] t
    | Case_ Type Multiplicity t  (NE.NonEmpty (TypedCaseBranchF t))
    | Application_ Type t t
    | Lambda_ Type Multiplicity Pattern t
    | Variable_ Type Identifier
    | Tuple_ Type [t]
    | Literal_ Type PrimitiveLiteral

type TypedExpr = Fix TypedExprF

pattern Let t binds body = Fix (Let_ t binds body)
pattern Case t mul disc branches = Fix (Case_ t mul disc branches)
pattern Application t fun arg = Fix (Application_ t fun arg)
pattern Lambda t mul pat body = Fix (Lambda_ t mul pat body)
pattern Variable t name = Fix (Variable_ t name)
pattern Tuple t es = Fix (Tuple_ t es)
pattern Literal t lit = Fix (Literal_ t lit)

instance Show t => Show (TypedExprF t) where
    show (Let_ _ binds body) = "let " ++ intercalate " and " (map show binds) ++ " in " ++ show body
    show (Case_ _ mul disc branches) = "case " ++ show mul ++ " " ++ show disc ++ " of " ++ intercalate "; " (map show (NE.toList branches))
    show (Application_ _ fun arg) = "(" ++ show fun ++ " " ++ show arg ++ ")"
    show (Lambda_ _ mul pat body) = "\\" ++ show pat ++ " -> " ++ show mul ++ " " ++ show body
    show (Variable_ _ name) = show name
    show (Tuple_ _ es) = "(" ++ intercalate ", " (map show es) ++ ")"
    show (Literal_ _ lit) = show lit

instance Show1 TypedExprF where
    liftShowsPrec sp sl d (Let_ _ binds body) =
        showString "let " . foldl (.) id (intersperse (showString " and ") (map (liftShowsPrec sp sl d) binds))
        . showString " in " . sp d body -- foldl (.) id (intersperse (showString " and ") (map (fmap (sp d)) binds))
    liftShowsPrec sp sl d (Case_ _ mul disc branches) =
        showString "case " . showString (show mul) . showString " " . sp d disc . showString " of "
        . foldl (.) id (intersperse (showString "; ") (map (liftShowsPrec sp sl d) (NE.toList branches)))
    liftShowsPrec sp _ d (Application_ _ fun arg) = showParen True (sp d fun . sp d arg)
    liftShowsPrec sp _ d (Lambda_ _ mul pat body) =
        showString "\\" . showString (show pat) . showString " -> " . showString (show mul) . sp d body
    liftShowsPrec _ _ _ (Variable_ _ name) = showString (show name)
    liftShowsPrec sp sl d (Tuple_ _ ts) =
        showString "(" . foldl (.) id (intersperse (showString ", ") (map (sp d) ts))
    liftShowsPrec _ _ _ (Literal_ _ lit) = showString (show lit)
    

instance TypeContainer t => TypeContainer (TypedExprF t) where
    typeof (Let_ t _ _) = t
    typeof (Case_ t _ _ _) = t
    typeof (Application_ t _ _) = t
    typeof (Lambda_ t _ _ _) = t
    typeof (Variable_ t _) = t
    typeof (Tuple_ t _) = t
    typeof (Literal_ t _) = t

instance Functor TypedExprF where
    fmap f (Let_ t binds body) = Let_ t (map (fmap f) binds) (f body)
    fmap f (Case_ t mul disc branches) = Case_ t mul (f disc) (NE.map (fmap f) branches)
    fmap f (Application_ t fun arg) = Application_ t (f fun) (f arg)
    fmap f (Lambda_ t mul pat body) = Lambda_ t mul pat (f body)
    fmap _ (Variable_ t name) = Variable_ t name
    fmap f (Tuple_ t es) = Tuple_ t (fmap f es)
    fmap _ (Literal_ t lit) = Literal_ t lit

instance Foldable TypedExprF where
    foldr f e (Let_ _ binds body) = foldl (foldr f) (f body e) binds
    foldr f e (Case_ _ _ disc branches) = f disc (foldl (foldr f) e branches)
    foldr f e (Application_ _ fun arg) = f fun (f arg e)
    foldr f e (Lambda_ _ _ _ body) = f body e
    foldr _ e (Variable_ _ _) = e
    foldr f e (Tuple_ _ es) = foldr f e es
    foldr _ e (Literal_ _ _) = e

instance Traversable TypedExprF where
    traverse f (Let_ t binds body) = Let_ t <$> traverse (traverse f) binds <*> f body
    traverse f (Case_ t mul disc branches) = Case_ t mul <$> f disc <*> traverse (traverse f) branches
    traverse f (Application_ t fun arg) = Application_ t <$> f fun <*> f arg
    traverse f (Lambda_ t mul pat body) = Lambda_ t mul pat <$> f body
    traverse _ (Variable_ t name) = pure (Variable_ t name)
    traverse f (Tuple_ t es) = Tuple_ t <$> traverse f es
    traverse _ (Literal_ t lit) = pure (Literal_ t lit)

data TypedLetBindingF t = TypedLetBinding Multiplicity Pattern t

type TypedLetBinding = TypedLetBindingF TypedExpr

instance Show t => Show (TypedLetBindingF t) where
    show (TypedLetBinding mul pat body) = show mul ++ " " ++ show pat ++ " = " ++ show body

instance Show1 TypedLetBindingF where
    liftShowsPrec sp _ d (TypedLetBinding mul pat body) =
        showString (show mul) . showString " " . showString (show pat) . showString " = " . sp d body

instance TypeContainer t => TypeContainer (TypedLetBindingF t) where
    typeof (TypedLetBinding _ _ e) = typeof e

instance Functor TypedLetBindingF where
    fmap f (TypedLetBinding mul pat body) = TypedLetBinding mul pat (f body)

instance Foldable TypedLetBindingF where
    foldr f e (TypedLetBinding _ _ body) = f body e

instance Traversable TypedLetBindingF where
    traverse f (TypedLetBinding mul pat body) = TypedLetBinding mul pat <$> f body

data TypedCaseBranchF t = TypedCaseBranch Pattern t

type TypedCaseBranch = TypedCaseBranchF TypedExpr

instance Show t => Show (TypedCaseBranchF t) where
    show (TypedCaseBranch pat body) = show pat ++ " -> " ++ show body

instance Show1 TypedCaseBranchF where
    liftShowsPrec sp _ d (TypedCaseBranch pat body) =
        showString (show pat) . showString " -> " . sp d body

instance TypeContainer t => TypeContainer (TypedCaseBranchF t) where
    typeof (TypedCaseBranch _ e) = typeof e

instance Functor TypedCaseBranchF where
    fmap f (TypedCaseBranch pat body) = TypedCaseBranch pat (f body)

instance Foldable TypedCaseBranchF where
    foldr f e (TypedCaseBranch _ body) = f body e

instance Traversable TypedCaseBranchF where
    traverse f (TypedCaseBranch pat body) = TypedCaseBranch pat <$> f body

data Pattern
    = VariablePattern Type Identifier
    | ConstructorPattern Identifier [Pattern]
    | LiteralPattern (Literal Pattern)

instance Show Pattern where
    show (VariablePattern t name) = "(" ++ show name ++ " : " ++ show t ++ ")"
    show (ConstructorPattern name ps) = "(" ++ show name ++ " " ++ unwords (map show ps) ++ ")"
    show (LiteralPattern lit) = show lit

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
    deriving Show

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
    -- , _mulEquivalences      :: DM.DisjointMap MultiplicityVar Multiplicity
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
    , _dataConstructors :: M.HashMap Identifier (TypeScheme, [Type])
    , _dataTypes :: M.HashMap Identifier (S.HashSet TypeVar, [(Identifier, (TypeScheme, [Type]))])
    }
    deriving Show

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

intType, realType, unitType, boolType, listTypeCon :: Type
intType = Ground (I "Int")
realType = Ground (I "Real")
unitType = Ground (I "()")
boolType = Ground (I "Bool")
listTypeCon = Ground (I "[]")

type TypeBuilder a = State ( (Integer, M.HashMap Identifier Integer)
                           , (Integer, M.HashMap Identifier Integer)
                           ) a

typeExprToScheme :: Loc TypeExpr -> (TypeScheme, [Type])
typeExprToScheme tExpr =
    let startState = ((0, M.empty), (0, M.empty))
        (t, ((tvars, _), (mvars, _))) = runState (buildTypeFor tExpr) startState
     in (TypeScheme (S.fromList [0..(tvars-1)]) (S.fromList [0..(mvars-1)]) t, findArgTypes t)
    where
        buildTypeFor :: Loc TypeExpr -> TypeBuilder Type
        buildTypeFor (L _ (TEGround name)) = pure (Ground name)
        buildTypeFor (L _ (TEPoly name)) = do
            nameMap <- gets (snd . fst)
            case M.lookup name nameMap of
              Just id -> pure (Poly id)
              Nothing -> do
                  id <- gets (fst . fst)
                  modify (first (bimap (+1) (M.insert name id)))
                  pure (Poly id)
        buildTypeFor (L _ (TEApp fun arg)) = do
            TypeApp <$> buildTypeFor fun <*> buildTypeFor arg
        buildTypeFor (L _ (TEArrow from mul to)) = do
            FunctionType <$> buildTypeFor from <*> buildArrowFor mul <*> buildTypeFor to
        buildTypeFor (L _ TEUnit) = pure unitType
        buildTypeFor (L _ (TETuple ts)) = TupleType <$> mapM buildTypeFor ts
        buildTypeFor (L _ (TEList t)) = TypeApp listTypeCon <$> buildTypeFor t

        buildArrowFor :: Loc ArrowExpr -> TypeBuilder Arrow
        buildArrowFor (L _ (ArrowExpr Nothing)) = pure (Arrow (MAtom Normal))
        buildArrowFor (L _ (ArrowExpr (Just (L _ m)))) = Arrow <$> buildMulFor m

        buildMulFor :: MultiplicityExpr -> TypeBuilder Multiplicity
        buildMulFor (MEPoly name) = do
            nameMap <- gets (snd . snd)
            case M.lookup name nameMap of
              Just id -> pure (MPoly id)
              Nothing -> do
                  id <- gets (fst . snd)
                  modify (second (bimap (+1) (M.insert name id)))
                  pure (MPoly id)
        buildMulFor (MEAtom atom) = pure (MAtom atom)
        buildMulFor (MEProd lhs rhs) = MProd <$> buildMulFor lhs <*> buildMulFor rhs

        findArgTypes :: Type -> [Type]
        findArgTypes (FunctionType from _ to) = from : findArgTypes to
        findArgTypes _ = []

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
showError text tvm (MissingType loc name) = 
    showContext text loc ++ "Type constructor \"" ++ show name ++ "\" not in scope."
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
    showContext text loc ++ "Inferred type \"" ++ showType tvm t ++ "\" cannot entail annotated type."
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

