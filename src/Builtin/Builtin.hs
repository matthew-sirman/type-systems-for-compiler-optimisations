module Builtin.Builtin where

-- Builtin functions and types which are non-definable in the syntax
-- or expected to be available without any imports

import Typing.Types
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
    , funcCompare
    , funcAdd
    , funcSub
    , funcMul
    , funcDiv
    , funcMod
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
    , typeUInt
    , typeReal
    , typeUReal
    ]

funcEquals, funcNotEquals, funcGreaterThan, funcLessThan, funcGreaterEqual, funcLessEqual,
    funcCompare, funcAdd, funcSub, funcMul, funcDiv, funcMod, funcUndefined :: BuiltinFunction
funcEquals       = (I "==#", makeScheme "Int# -o Int# -o Int#")
funcNotEquals    = (I "!=#", makeScheme "Int# -o Int# -o Int#")
funcGreaterThan  = (I ">#", makeScheme "Int# -o Int# -o Int#")
funcLessThan     = (I "<#", makeScheme "Int# -o Int# -o Int#")
funcGreaterEqual = (I ">=#", makeScheme "Int# -o Int# -o Int#")
funcLessEqual    = (I "<=#", makeScheme "Int# -o Int# -o Int#")
funcCompare      = (I "<=>#", makeScheme "Int# -o Int# -o Int#")
funcAdd          = (I "+#", makeScheme "Int# -o Int# -o Int#")
funcSub          = (I "-#", makeScheme "Int# -o Int# -o Int#")
funcMul          = (I "*#", makeScheme "Int# -o Int# -o Int#")
funcDiv          = (I "/#", makeScheme "Int# -o Int# -o Int#")
funcMod          = (I "%#", makeScheme "Int# -o Int# -o Int#")
funcUndefined    = (I "undefined", makeScheme "a")

consUnit, consTrue, consFalse, consListNil, consListCons, consMkInt, consMkReal :: BuiltinConstructor
consUnit = (I "()", makeConsScheme "()")
consTrue = (I "True", makeConsScheme "Bool")
consFalse = (I "False", makeConsScheme "Bool")
consListNil = (I "[]", makeConsScheme "[a]")
consListCons = (I "::", makeConsScheme "a -o [a] -o [a]")
consMkInt = (I "MkInt#", makeConsScheme "Int# -o Int")
consMkReal = (I "MkReal#", makeConsScheme "Real# -o Real")

typeUnit, typeBool, typeListCons, typeInt, typeUInt, typeReal, typeUReal :: BuiltinType
typeUnit = (I "()", collectTypeVars [consUnit])
typeBool = (I "Bool", collectTypeVars [consFalse, consTrue])
typeListCons = (I "[]", collectTypeVars [consListNil, consListCons])
typeInt = (I "Int", collectTypeVars [consMkInt])
typeUInt = (I "Int#", (S.empty, []))
typeReal = (I "Real", collectTypeVars [consMkReal])
typeUReal = (I "Real#", (S.empty, []))

makeScheme :: String -> TypeScheme
makeScheme = fst . makeConsScheme

makeConsScheme :: String -> (TypeScheme, [Type])
makeConsScheme typeString = case parseType typeString of
                              Right tExpr -> typeExprToScheme tExpr

collectTypeVars :: [BuiltinConstructor] -> (S.HashSet TypeVar, [BuiltinConstructor])
collectTypeVars conss = (S.unions (map ((^. quantifiedTVars) . fst . snd) conss), conss)

