{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving #-}
module IR.Instructions where

import IR.DataType

import Data.List (intercalate)
import Data.Word
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

newtype FunctionID = FID String
    deriving (Eq, Ord, Generic)

instance Show FunctionID where
    show (FID name) = name

instance Hashable FunctionID

newtype Label = Label String
    deriving (Eq, Semigroup, Monoid, Generic)

instance Show Label where
    show (Label name) = name

instance Hashable Label

data Immediate
    = Int64 Int
    | Real64 Double
    | Int1 Bool
    | Unit
    | Undef

instance Show Immediate where
    show (Int64 i) = "i64 " ++ show i
    show (Real64 r) = "r64 " ++ show r
    show (Int1 b) = "i1 " ++ if b then "1" else "0"
    show Unit = "unit ()"
    show Undef = "***UNDEF***"

data Value r
    = ValImmediate Immediate
    | ValVariable DataType r
    | ValFunction DataType FunctionID
    | ValSizeOf DataType

instance Show r => Show (Value r) where
    show (ValImmediate i) = show i
    show (ValVariable dt r) = show dt ++ " " ++ show r
    show (ValFunction _ fn) = "&" ++ show fn
    show (ValSizeOf dt) = "sizeof(" ++ show dt ++ ")"

dataType :: Value r -> DataType
dataType (ValImmediate (Int64 _)) = FirstOrder Int64T
dataType (ValImmediate (Real64 _)) = FirstOrder Real64T
dataType (ValImmediate (Int1 _)) = FirstOrder Int1T
dataType (ValImmediate Unit) = FirstOrder UnitT
dataType (ValImmediate Undef) = FirstOrder Void
dataType (ValVariable t _) = t
dataType (ValFunction t _) = t
dataType (ValSizeOf _) = FirstOrder Int64T

newtype PhiNode r = PhiNode (Value r, Label)

instance Show r => Show (PhiNode r) where
    show (PhiNode (val, label)) = show val ++ " : " ++ show label

data Instruction r
    = Binop BinaryOperator r (Value r) (Value r)
    | Move r (Value r)
    | Write (Value r) (Value r) DataType
    | Read r (Value r) DataType
    | GetElementPtr r (Value r) [Int]
    | BitCast r (Value r) DataType
    | MAlloc r (Value r)
    | Free (Value r)
    | Call (Maybe r) (Value r) [Value r]
    | Branch (Value r) Label
    | Jump Label
    | Phi r [PhiNode r]
    | Return (Maybe (Value r))
    | Throw Int

instance Show r => Show (Instruction r) where
    show (Binop op res e1 e2) = show res ++ " = " ++ show op ++ " " ++ show e1 ++ ", " ++ show e2
    show (Move res e) = "mov " ++ show res ++ ", " ++ show e
    show (Write val addr dt) = "wr " ++ show val ++ ", " ++ show dt ++ " (" ++ show addr ++ ")"
    show (Read res loc dt) = show res ++ " <- rd " ++ show dt ++ " (" ++ show loc ++ ")"
    show (GetElementPtr res val path) = show res ++ " = getelementptr " ++ show val ++ ", " ++ intercalate ", " (map show path)
    show (BitCast res val dt) = show res ++ " = bitcast " ++ show val ++ " to " ++ show dt
    show (MAlloc res size) = show res ++ " = malloc " ++ show size
    show (Free ptr) = "free " ++ show ptr
    show (Call res func args) = resStr ++ "call " ++ show func ++ "(" ++ intercalate ", " (map show args) ++ ")"
        where
            resStr = case res of
                       Nothing -> ""
                       Just r -> show r ++ " = "
    show (Branch val label) = "br " ++ show val ++ ", " ++ show label
    show (Jump label) = "br " ++ show label
    show (Phi res ps) = show res ++ " = phi [" ++ intercalate ", " (map show ps) ++ "]"
    show (Return Nothing) = "ret"
    show (Return (Just val)) = "ret " ++ show val
    show (Throw err) = "throw " ++ show err

data BinaryOperator
    = Add
    | Sub
    | Mul
    | Div
    | And
    | Or
    | Shift
    | Equal
    | NotEqual
    | LessThan
    | GreaterThan
    | LessThanEqual
    | GreaterThanEqual

instance Show BinaryOperator where
    show Add = "add"
    show Sub = "sub"
    show Mul = "mul"
    show Div = "div"
    show And = "and"
    show Or = "or"
    show Shift = "shift"
    show Equal = "eq"
    show NotEqual = "neq"
    show LessThan = "lt"
    show GreaterThan = "gt"
    show LessThanEqual = "le"
    show GreaterThanEqual = "gt"

