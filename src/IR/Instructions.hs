{-# LANGUAGE DeriveGeneric, GeneralizedNewtypeDeriving, TemplateHaskell, ScopedTypeVariables #-}
module IR.Instructions where

-- Data types for STFL-IR instruction set

import IR.DataType

import Data.List (intercalate)
import Data.Word
import Data.Hashable (Hashable)

import Control.Lens

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
    | ValGlobal (GlobalBlock r)
    | ValFunction DataType FunctionID
    | ValSizeOf DataType

instance Show r => Show (Value r) where
    show (ValImmediate i) = show i
    show (ValVariable dt r) = show dt ++ " " ++ show r
    show (ValGlobal block) = _globalName block
    show (ValFunction _ fn) = "&" ++ show fn
    show (ValSizeOf dt) = "sizeof(" ++ show dt ++ ")"

instance DataTypeContainer (Value r) where
    datatype (ValImmediate (Int64 _)) = I64
    datatype (ValImmediate (Real64 _)) = R64
    datatype (ValImmediate (Int1 _)) = I1
    datatype (ValImmediate Unit) = FirstOrder UnitT
    datatype (ValImmediate Undef) = Void
    datatype (ValGlobal block) = Pointer (Structure (map datatype (_blockData block)))
    datatype (ValVariable t _) = t
    datatype (ValFunction t _) = t
    datatype (ValSizeOf _) = I64

data GlobalBlock r = GlobalBlock
    { _globalName :: String
    , _blockData :: [Value r]
    }

makeLenses ''GlobalBlock

instance Show r => Show (GlobalBlock r) where
    show global = global ^. globalName ++ " = global {" ++ intercalate ", " (map show (global ^. blockData)) ++ "}\n"

newtype PhiNode r = PhiNode (Value r, Label)

instance Show r => Show (PhiNode r) where
    show (PhiNode (val, label)) = show val ++ " : " ++ show label

data Instruction r e
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
    | Push (Value r)
    | Pop DataType r
    | PrintF String [Value r]
    | Throw e
    | Comment String

instance (Show r, Show e) => Show (Instruction r e) where
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
    show (Push val) = "push " ++ show val
    show (Pop dt res) = show res ++ " <- pop " ++ show dt
    show (PrintF fmt []) = "call printf(" ++ show fmt ++ ")"
    show (PrintF fmt args) = "call printf(" ++ show fmt ++ ", " ++ intercalate ", " (map show args) ++ ")"
    show (Throw err) = "throw " ++ show err
    show (Comment comment) = "; " ++ comment

data BinaryOperator
    = Add
    | Sub
    | Mul
    | Div
    | Mod
    | And
    | Or
    | Shift
    | Equal
    | NotEqual
    | LessThan
    | GreaterThan
    | LessThanEqual
    | GreaterThanEqual
    | Compare

instance Show BinaryOperator where
    show Add = "add"
    show Sub = "sub"
    show Mul = "mul"
    show Div = "div"
    show Mod = "mod"
    show And = "and"
    show Or = "or"
    show Shift = "shift"
    show Equal = "eq"
    show NotEqual = "neq"
    show LessThan = "lt"
    show GreaterThan = "gt"
    show LessThanEqual = "le"
    show GreaterThanEqual = "gt"
    show Compare = "cmp"

