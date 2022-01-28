module Compiler.Size where

import Parser.AST (Identifier(..))
import Typing.Types

pointerSize :: Num a => a
pointerSize = 8

int64Size, realSize, unitSize, boolSize :: Num a => a
int64Size = 8
realSize = 8
unitSize = 0
boolSize = 1

sizeof :: Num a => Type -> a
sizeof (Poly _) = pointerSize
sizeof (Ground (I name))
    | name == "Int" = int64Size
    | name == "Real" = realSize
    | name == "()" = unitSize
    | name == "Bool" = boolSize
-- TODO: Handle other ground types propetly

-- TODO: Handle type applications properly
sizeof (TypeApp _ _) = undefined
-- TODO: Handle function data properly (maybe this will actually
--      need to store a closure?)
sizeof (FunctionType {}) = pointerSize
sizeof (TupleType ts) = sum (map sizeof ts)

