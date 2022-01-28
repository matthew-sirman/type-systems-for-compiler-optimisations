{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving #-}
module IR.Instructions where

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
    | Bool Bool
    | Unit

instance Show Immediate where
    show (Int64 i) = "i64 " ++ show i
    show (Real64 r) = "r64 " ++ show r
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
    | Write (Value r) (Value r) Word64
    | Read r (Value r) Word64
    | MAlloc r (Value r)
    | Call (Maybe r) (Value r) [Value r]
    | Branch (Value r) Label
    | Jump Label
    | Phi r [PhiNode r]
    | Return (Maybe (Value r))
    | Throw Int

instance Show r => Show (Instruction r) where
    show (Binop op res e1 e2) = show res ++ " = " ++ show op ++ " " ++ show e1 ++ ", " ++ show e2
    show (Move res e) = "mov " ++ show res ++ ", " ++ show e
    show (Write val addr size) = "wr " ++ show size ++ " " ++ show val ++ ", (" ++ show addr ++ ")"
    show (Read res loc size) = show res ++ " <- rd " ++ show size ++ " (" ++ show loc ++ ")"
    show (MAlloc res size) = show res ++ " = malloc " ++ show size
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

