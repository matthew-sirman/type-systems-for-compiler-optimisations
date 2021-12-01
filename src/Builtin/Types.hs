module Builtin.Types
    ( intType
    , realType
    , unitType
    , boolType
    , listTypeCon
    ) where

import Typing.Types
import Parser.AST (Identifier(..))

intType, realType, unitType, boolType, listTypeCon :: Type
intType = Ground (I "Int")
realType = Ground (I "Real")
unitType = Ground (I "()")
boolType = Ground (I "Bool")
listTypeCon = Ground (I "[]")

