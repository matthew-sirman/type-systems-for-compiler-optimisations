{-# LANGUAGE DeriveGeneric #-}
module IR.Instructions where

import Data.List (intercalate)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

newtype FunctionID = FID String
    deriving (Eq, Ord, Generic)

instance Show FunctionID where
    show (FID name) = name

instance Hashable FunctionID

newtype Label = Label String

instance Show Label where
    show (Label name) = name

data Immediate
    = Int64 Int
    | Bool Bool
    | Unit

instance Show Immediate where
    show (Int64 i) = "i64 " ++ show i
    show (Bool b) = "i1 " ++ if b then "1" else "0"
    show Unit = "unit ()"

data Closure r
    = Closure FunctionID (Maybe r)

instance Show r => Show (Closure r) where
    show (Closure func Nothing) = show func
    show (Closure func (Just v)) = show func ++ "(cl: " ++ show v ++ ")"

data Value r
    = ValImmediate Immediate
    | ValVariable r
    | ValClosure (Closure r)

instance Show r => Show (Value r) where
    show (ValImmediate i) = show i
    show (ValVariable r) = show r
    show (ValClosure cl) = show cl

newtype PhiNode r = PhiNode (Value r, Label)

instance Show r => Show (PhiNode r) where
    show (PhiNode (val, label)) = show val ++ " : " ++ show label

data Instruction r
    = Binop BinaryOperator r (Value r) (Value r)
    | Move r (Value r)
    | Write (Value r) (Value r) Int
    | Read r (Value r) Int
    | MAlloc r (Value r)
    | Call r (Value r) [Value r]
    | Branch (Value r) Label
    | Jump Label
    | Phi r (PhiNode r) (PhiNode r)
    | Return (Value r)
    | Push (Value r)
    | Pop r

instance Show r => Show (Instruction r) where
    show (Binop op res e1 e2) = show res ++ " = " ++ show op ++ " " ++ show e1 ++ ", " ++ show e2
    show (Move res e) = "mov " ++ show res ++ ", " ++ show e
    show (Write val addr size) = "wr " ++ show size ++ " " ++ show val ++ ", (" ++ show addr ++ ")"
    show (Read res loc size) = "rd " ++ show size ++ " " ++ show res ++ " <- (" ++ show loc ++ ")"
    show (MAlloc res size) = show res ++ " = malloc " ++ show size
    show (Call res func args) = show res ++ " = call " ++ show func ++ "(" ++ intercalate ", " (map show args) ++ ")"
    show (Branch val label) = "br " ++ show val ++ ", " ++ show label
    show (Jump label) = "br " ++ show label
    show (Phi res p1 p2) = show res ++ " = phi [" ++ show p1 ++ ", " ++ show p2 ++ "]"
    show (Return val) = "ret " ++ show val
    show (Push val) = "push " ++ show val
    show (Pop res) = "pop " ++ show res

data BinaryOperator
    = Add
    | Sub
    | Mul
    | Div
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
    show Equal = "eq"
    show NotEqual = "neq"
    show LessThan = "lt"
    show GreaterThan = "gt"
    show LessThanEqual = "le"
    show GreaterThanEqual = "gt"
