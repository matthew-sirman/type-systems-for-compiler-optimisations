module Builtin.Builtin where
     -- ( defaultBuiltins
     -- ) where

import Typing.Types
import Builtin.Types
import Parser.AST (Identifier(..), MultiplicityAtom(..))

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

type BuiltinFunction = (Identifier, TypeScheme)

defaultBuiltins :: StaticContext
defaultBuiltins = StaticContext functions constructors types

functions :: M.HashMap Identifier TypeScheme
functions = M.fromList
    [ funcEquals
    , funcNotEquals
    , funcGreaterThan
    , funcLessThan
    , funcGreaterEqual
    , funcLessEqual
    , funcAdd
    , funcSub
    , funcMul
    , funcDiv
    , funcUndefined
    ]

constructors :: M.HashMap Identifier TypeScheme
constructors = M.fromList
    [ consTrue
    , consFalse
    , consListNil
    , consListCons
    ]

types :: S.HashSet Identifier
types = S.empty

funcEquals, funcNotEquals, funcGreaterThan, funcLessThan, funcGreaterEqual, funcLessEqual,
    funcAdd, funcSub, funcMul, funcDiv, funcUndefined :: BuiltinFunction
funcEquals = (I "==", TypeScheme (S.singleton 0) S.empty (FunctionType a linear (FunctionType a linear boolType)))
funcNotEquals = (I "!=", TypeScheme (S.singleton 0) S.empty (FunctionType a linear (FunctionType a linear boolType)))
funcGreaterThan = (I ">", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear boolType)))
funcLessThan = (I "<", TypeScheme S.empty S.empty  (FunctionType intType linear (FunctionType intType linear boolType)))
funcGreaterEqual = (I ">=", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear boolType)))
funcLessEqual = (I "<=", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear boolType)))
funcAdd = (I "+", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear intType)))
funcSub = (I "-", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear intType)))
funcMul = (I "*", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear intType)))
funcDiv = (I "/", TypeScheme S.empty S.empty (FunctionType intType linear (FunctionType intType linear intType)))
funcUndefined = (I "undefined", TypeScheme (S.singleton 0) S.empty (Poly 0))

consTrue, consFalse, consListNil, consListCons :: BuiltinFunction
consTrue = (I "True", normalCons [] boolType)
consFalse = (I "False", normalCons [] boolType)
consListNil = (I "[]", normalCons [] (list a))
consListCons = (I "::", normalCons [a, list a] (list a))

normalCons :: [Type] -> Type -> TypeScheme
normalCons args result = TypeScheme (ftv args `S.union` ftv result) S.empty (consType args)
    where
        consType :: [Type] -> Type
        consType [] = result
        consType (t:ts) = FunctionType t linear (consType ts)

normal, linear :: Arrow
linear = Arrow (MAtom Linear)
normal = Arrow (MAtom Normal)

a :: Type
a = Poly 0

list :: Type -> Type
list = TypeApp listTypeCon

