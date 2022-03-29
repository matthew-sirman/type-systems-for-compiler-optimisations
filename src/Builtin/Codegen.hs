{-# LANGUAGE RankNTypes #-}
module Builtin.Codegen where

import Parser.AST (Identifier(..))
import qualified IR.Instructions as IR
import qualified IR.InstructionBuilder as IR
import qualified IR.DataType as IR

import qualified Data.HashMap.Strict as M

newtype PrimitiveFunction r = PrimitiveFunction
    { mkPrim :: forall m. IR.MonadIRBuilder r m => m r -> [IR.Value r] -> m (IR.Value r) }

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
funcUndefined    = (I "undefined", undefinedGen)

binopFunction :: IR.BinaryOperator -> PrimitiveFunction r
binopFunction op = PrimitiveFunction $ \getReg [lhs, rhs] ->
    IR.binop op getReg lhs rhs

undefinedGen :: PrimitiveFunction r
undefinedGen = PrimitiveFunction $ \_ _ -> do
    IR.throw 2
    pure (IR.ValImmediate IR.Unit)

thunkTagStruct :: IR.Struct
thunkTagStruct = IR.Struct "thunk_tag" [IR.FirstOrder IR.Int1T] True

