module Builtin.Codegen where

import Parser.AST (Identifier(..))
import qualified IR.Instructions as IR

import qualified Data.HashMap.Strict as M

type PrimitiveFunction r = r -> [IR.Value r] -> IR.Instruction r

functions :: M.HashMap Identifier (PrimitiveFunction r)
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

funcEquals, funcNotEquals, funcGreaterThan, funcLessThan, funcGreaterEqual, funcLessEqual,
    funcAdd, funcSub, funcMul, funcDiv, funcUndefined :: (Identifier, PrimitiveFunction r)
funcEquals       = (I "==", binopFunction IR.Equal)
funcNotEquals    = (I "!=", binopFunction IR.NotEqual)
funcGreaterThan  = (I ">", binopFunction IR.GreaterThan)
funcLessThan     = (I "<", binopFunction IR.LessThan)
funcGreaterEqual = (I ">=", binopFunction IR.GreaterThanEqual)
funcLessEqual    = (I "<=", binopFunction IR.LessThanEqual)
funcAdd          = (I "+", binopFunction IR.Add)
funcSub          = (I "-", binopFunction IR.Sub)
funcMul          = (I "*", binopFunction IR.Mul)
funcDiv          = (I "/", binopFunction IR.Div)
funcUndefined    = (I "undefined", \_ _ -> IR.Throw 2)

binopFunction :: IR.BinaryOperator -> PrimitiveFunction r
binopFunction op res [lhs, rhs] = IR.Binop op res lhs rhs

