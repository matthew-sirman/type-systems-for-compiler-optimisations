module Builtin.Builtin where
     -- ( defaultBuiltins
     -- ) where

import Typing.Types
import Parser.AST (Identifier(..), Multiplicity(..), MultiplicityAtom(..))

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
    funcAdd, funcSub, funcMul, funcDiv :: BuiltinFunction
funcEquals = (I "==", TypeScheme [0] (FunctionType a linear (FunctionType a linear boolType)))
funcNotEquals = (I "!=", TypeScheme [0] (FunctionType a linear (FunctionType a linear boolType)))
funcGreaterThan = (I ">", TypeScheme [] (FunctionType intType linear (FunctionType intType linear boolType)))
funcLessThan = (I "<", TypeScheme [] (FunctionType intType linear (FunctionType intType linear boolType)))
funcGreaterEqual = (I ">=", TypeScheme [] (FunctionType intType linear (FunctionType intType linear boolType)))
funcLessEqual = (I "<=", TypeScheme [] (FunctionType intType linear (FunctionType intType linear boolType)))
funcAdd = (I "+", TypeScheme [] (FunctionType intType linear (FunctionType intType linear intType)))
funcSub = (I "-", TypeScheme [] (FunctionType intType linear (FunctionType intType linear intType)))
funcMul = (I "*", TypeScheme [] (FunctionType intType linear (FunctionType intType linear intType)))
funcDiv = (I "/", TypeScheme [] (FunctionType intType linear (FunctionType intType linear intType)))

consTrue, consFalse, consListNil, consListCons :: BuiltinFunction
consTrue = (I "True", normalCons [] boolType)
consFalse = (I "False", normalCons [] boolType)
consListNil = (I "[]", normalCons [] (list a))
consListCons = (I "::", normalCons [a, list a] (list a))

normalCons :: [Type] -> Type -> TypeScheme
normalCons args result = TypeScheme (S.toList (ftv args `S.union` ftv result)) (consType args)
    where
        consType :: [Type] -> Type
        consType [] = result
        consType (t:ts) = FunctionType t linear (consType ts)

normal, linear :: Arrow
linear = Arrow (Just (MAtom Linear))
normal = Arrow (Just (MAtom Normal))

a :: Type
a = Poly 0

list :: Type -> Type
list = TypeApp listTypeCon

