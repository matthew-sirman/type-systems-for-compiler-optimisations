{-# LANGUAGE RankNTypes #-}
module Builtin.Codegen where

-- Code generation helpers for primitive functions

import Parser.AST (Identifier(..))
import qualified IR.Instructions as IR
import qualified IR.InstructionBuilder as IR
import qualified IR.DataType as IR

import qualified Data.HashMap.Strict as M

data PrimitiveFunction
    = Equal
    | NotEqual
    | GreaterThan
    | LessThan
    | GreaterThanEqual
    | LessThanEqual
    | Compare
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | Undefined

instance Show PrimitiveFunction where
    show Equal = "==#"
    show NotEqual = "!=#"
    show GreaterThan = ">#"
    show LessThan = "<#"
    show GreaterThanEqual = ">=#"
    show LessThanEqual = "<=#"
    show Compare = "<=>#"
    show Add = "+#"
    show Sub = "-#"
    show Mul = "*#"
    show Div = "/#"
    show Mod = "%#"
    show Undefined = "undefined#"

getPrimitive :: Identifier -> Maybe PrimitiveFunction
getPrimitive (I "==#") = Just Equal
getPrimitive (I "!=#") = Just NotEqual
getPrimitive (I ">#") = Just GreaterThan
getPrimitive (I "<#") = Just LessThan
getPrimitive (I ">=#") = Just GreaterThanEqual
getPrimitive (I "<=#") = Just LessThanEqual
getPrimitive (I "<=>#") = Just Compare
getPrimitive (I "+#") = Just Add
getPrimitive (I "-#") = Just Sub
getPrimitive (I "*#") = Just Mul
getPrimitive (I "/#") = Just Div
getPrimitive (I "%#") = Just Mod
getPrimitive (I "undefined") = Just Undefined
getPrimitive _ = Nothing

generatePrimitive :: IR.MonadIRBuilder r e m => m r -> PrimitiveFunction -> [IR.Value r] -> m (IR.Value r)
generatePrimitive getReg Equal [lhs, rhs] = IR.binop IR.Equal getReg lhs rhs
generatePrimitive getReg NotEqual [lhs, rhs] = IR.binop IR.NotEqual getReg lhs rhs
generatePrimitive getReg GreaterThan [lhs, rhs] = IR.binop IR.GreaterThan getReg lhs rhs
generatePrimitive getReg LessThan [lhs, rhs] = IR.binop IR.LessThan getReg lhs rhs
generatePrimitive getReg GreaterThanEqual [lhs, rhs] = IR.binop IR.GreaterThanEqual getReg lhs rhs
generatePrimitive getReg LessThanEqual [lhs, rhs] = IR.binop IR.LessThanEqual getReg lhs rhs
generatePrimitive getReg Compare [lhs, rhs] = IR.binop IR.Compare getReg lhs rhs
generatePrimitive getReg Add [lhs, rhs] = IR.binop IR.Add getReg lhs rhs
generatePrimitive getReg Sub [lhs, rhs] = IR.binop IR.Sub getReg lhs rhs
generatePrimitive getReg Mul [lhs, rhs] = IR.binop IR.Mul getReg lhs rhs
generatePrimitive getReg Div [lhs, rhs] = IR.binop IR.Div getReg lhs rhs
generatePrimitive getReg Mod [lhs, rhs] = IR.binop IR.Mod getReg lhs rhs
generatePrimitive _ Undefined _ = do
    IR.throwUndefined
    pure (IR.ValImmediate IR.Undef)

