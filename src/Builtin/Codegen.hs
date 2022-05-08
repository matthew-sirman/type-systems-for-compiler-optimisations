{-# LANGUAGE RankNTypes #-}
module Builtin.Codegen where

import Parser.AST (Identifier(..))
import qualified IR.Instructions as IR
import qualified IR.InstructionBuilder as IR
import qualified IR.DataType as IR

import qualified Data.HashMap.Strict as M

-- newtype PrimitiveFunction r = PrimitiveFunction
--     { mkPrim :: forall m. IR.MonadIRBuilder r m => m r -> [IR.Value r] -> m (IR.Value r) }

data PrimitiveFunction
    = Equal
    | NotEqual
    | GreaterThan
    | LessThan
    | GreaterThanEqual
    | LessThanEqual
    | Add
    | Sub
    | Mul
    | Div
    | Undefined

instance Show PrimitiveFunction where
    show Equal = "==#"
    show NotEqual = "!=#"
    show GreaterThan = ">#"
    show LessThan = "<#"
    show GreaterThanEqual = ">=#"
    show LessThanEqual = "<=#"
    show Add = "+#"
    show Sub = "-#"
    show Mul = "*#"
    show Div = "/#"
    show Undefined = "undefined#"

getPrimitive :: Identifier -> Maybe PrimitiveFunction
getPrimitive (I "==#") = Just Equal
getPrimitive (I "!=#") = Just NotEqual
getPrimitive (I ">#") = Just GreaterThan
getPrimitive (I "<#") = Just LessThan
getPrimitive (I ">=#") = Just GreaterThanEqual
getPrimitive (I "<=#") = Just LessThanEqual
getPrimitive (I "+#") = Just Add
getPrimitive (I "-#") = Just Sub
getPrimitive (I "*#") = Just Mul
getPrimitive (I "/#") = Just Div
getPrimitive (I "undefined") = Just Undefined
getPrimitive _ = Nothing

generatePrimitive :: IR.MonadIRBuilder r e m => m r -> PrimitiveFunction -> [IR.Value r] -> m (IR.Value r)
generatePrimitive getReg Equal [lhs, rhs] = IR.binop IR.Equal getReg lhs rhs
generatePrimitive getReg NotEqual [lhs, rhs] = IR.binop IR.NotEqual getReg lhs rhs
generatePrimitive getReg GreaterThan [lhs, rhs] = IR.binop IR.GreaterThan getReg lhs rhs
generatePrimitive getReg LessThan [lhs, rhs] = IR.binop IR.LessThan getReg lhs rhs
generatePrimitive getReg GreaterThanEqual [lhs, rhs] = IR.binop IR.GreaterThanEqual getReg lhs rhs
generatePrimitive getReg LessThanEqual [lhs, rhs] = IR.binop IR.LessThanEqual getReg lhs rhs
generatePrimitive getReg Add [lhs, rhs] = IR.binop IR.Add getReg lhs rhs
generatePrimitive getReg Sub [lhs, rhs] = IR.binop IR.Sub getReg lhs rhs
generatePrimitive getReg Mul [lhs, rhs] = IR.binop IR.Mul getReg lhs rhs
generatePrimitive getReg Div [lhs, rhs] = IR.binop IR.Div getReg lhs rhs
generatePrimitive _ Undefined _ = do
    IR.throwUndefined
    pure (IR.ValImmediate IR.Undef)

-- functions :: M.HashMap Identifier (PrimitiveFunction r)
-- functions = M.fromList
--     [ funcEquals
--     , funcNotEquals
--     , funcGreaterThan
--     , funcLessThan
--     , funcGreaterEqual
--     , funcLessEqual
--     , funcAdd
--     , funcSub
--     , funcMul
--     , funcDiv
--     , funcUndefined
--     ]
-- 
-- funcEquals, funcNotEquals, funcGreaterThan, funcLessThan, funcGreaterEqual, funcLessEqual,
--     funcAdd, funcSub, funcMul, funcDiv, funcUndefined :: (Identifier, PrimitiveFunction r)
-- funcEquals       = (I "==", binopFunction IR.Equal)
-- funcNotEquals    = (I "!=", binopFunction IR.NotEqual)
-- funcGreaterThan  = (I ">", binopFunction IR.GreaterThan)
-- funcLessThan     = (I "<", binopFunction IR.LessThan)
-- funcGreaterEqual = (I ">=", binopFunction IR.GreaterThanEqual)
-- funcLessEqual    = (I "<=", binopFunction IR.LessThanEqual)
-- funcAdd          = (I "+", binopFunction IR.Add)
-- funcSub          = (I "-", binopFunction IR.Sub)
-- funcMul          = (I "*", binopFunction IR.Mul)
-- funcDiv          = (I "/", binopFunction IR.Div)
-- funcUndefined    = (I "undefined", undefinedGen)
-- 
-- binopFunction :: IR.BinaryOperator -> PrimitiveFunction r
-- binopFunction op = PrimitiveFunction $ \getReg [lhs, rhs] ->
--     IR.binop op getReg lhs rhs
-- 
-- undefinedGen :: PrimitiveFunction r
-- undefinedGen = PrimitiveFunction $ \_ _ -> do
--     IR.throw 2
--     pure (IR.ValImmediate IR.Undef)

-- thunkTagStruct :: IR.Struct
-- thunkTagStruct = IR.Struct "thunk_tag" [] [IR.FirstOrder IR.Int1T] True

