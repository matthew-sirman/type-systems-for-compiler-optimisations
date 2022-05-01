module Builtin.Builtin where
     -- ( defaultBuiltins
     -- ) where

import Typing.Types
import Builtin.Types
import Parser.AST 
    ( Identifier(..)
    , Loc(..)
    , MultiplicityAtom(..)
    , TypeExpr(..)
    , ArrowExpr(..)
    , MultiplicityExpr(..)
    )
import Parser.Parser (parseType)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Bifunctor (bimap, first, second)

import Control.Monad.State
import Control.Lens

type BuiltinFunction = (Identifier, TypeScheme)
type BuiltinConstructor = (Identifier, (TypeScheme, [Type]))
type BuiltinType = (Identifier, (S.HashSet TypeVar, [BuiltinConstructor]))

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

constructors :: M.HashMap Identifier (TypeScheme, [Type])
constructors = M.fromList
    [ consUnit
    , consTrue
    , consFalse
    , consListNil
    , consListCons
    , consMkInt
    , consMkReal
    ]

types :: M.HashMap Identifier (S.HashSet TypeVar, [BuiltinConstructor])
types = M.fromList
    [ typeUnit
    , typeBool
    , typeListCons
    , typeInt
    , typeReal
    ]

funcEquals, funcNotEquals, funcGreaterThan, funcLessThan, funcGreaterEqual, funcLessEqual,
    funcAdd, funcSub, funcMul, funcDiv, funcUndefined :: BuiltinFunction
funcEquals       = (I "==#", makeScheme "Int# -o Int# -o Bool")
funcNotEquals    = (I "!=#", makeScheme "Int# -o Int# -o Bool")
funcGreaterThan  = (I ">#", makeScheme "Int# -o Int# -o Bool")
funcLessThan     = (I "<#", makeScheme "Int# -o Int# -o Bool")
funcGreaterEqual = (I ">=#", makeScheme "Int# -o Int# -o Bool")
funcLessEqual    = (I "<=#", makeScheme "Int# -o Int# -o Bool")
funcAdd          = (I "+#", makeScheme "Int# -o Int# -o Int#")
funcSub          = (I "-#", makeScheme "Int# -o Int# -o Int#")
funcMul          = (I "*#", makeScheme "Int# -o Int# -o Int#")
funcDiv          = (I "/#", makeScheme "Int# -o Int# -o Int#")
funcUndefined    = (I "undefined", makeScheme "a")

consUnit, consTrue, consFalse, consListNil, consListCons, consMkInt, consMkReal :: BuiltinConstructor
consUnit = (I "Unit", makeConsScheme "()")
consTrue = (I "True", makeConsScheme "Bool")
consFalse = (I "False", makeConsScheme "Bool")
consListNil = (I "[]", makeConsScheme "[a]")
consListCons = (I "::", makeConsScheme "a -o [a] -o [a]")
consMkInt = (I "MkInt#", makeConsScheme "Int# -o Int")
consMkReal = (I "MkReal#", makeConsScheme "Real# -o Real")

typeUnit, typeBool, typeListCons, typeInt, typeReal :: BuiltinType
typeUnit = (I "Unit", collectTypeVars [consUnit])
typeBool = (I "Bool", collectTypeVars [consFalse, consTrue])
typeListCons = (I "List", collectTypeVars [consListNil, consListCons])
typeInt = (I "Int", collectTypeVars [consMkInt])
typeReal = (I "Real", collectTypeVars [consMkReal])

makeScheme :: String -> TypeScheme
makeScheme = fst . makeConsScheme

makeConsScheme :: String -> (TypeScheme, [Type])
makeConsScheme typeString = case parseType typeString of
                              Right tExpr -> typeExprToScheme tExpr

collectTypeVars :: [BuiltinConstructor] -> (S.HashSet TypeVar, [BuiltinConstructor])
collectTypeVars conss = (S.unions (map ((^. quantifiedTVars) . fst . snd) conss), conss)

