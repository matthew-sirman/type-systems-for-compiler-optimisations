{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module IR.Function where

-- STFL-IR Function data type

import IR.Instructions
import IR.BasicBlock
import IR.DataType

import Data.Sequence as Seq
import Data.List (intercalate)
import Control.Lens

data Function r e = Function
    { _funcId :: FunctionID
    , _args :: [(r, DataType)]
    , _retType :: DataType
    , _blocks :: Seq (BasicBlock r e)
    }

makeLenses ''Function

instance (Show r, Show e) => Show (Function r e) where
    show fn = show (fn ^. retType) ++ " " ++ show (fn ^. funcId)
            ++ "(" ++ intercalate ", " (map showArg (fn ^. args)) ++ ") {\n" ++ concatMap show (fn ^. blocks) ++ "}\n\n"
        where
            showArg :: (r, DataType) -> String
            showArg (v, t) = show v ++ " : " ++ show t

makeFunc :: FunctionID -> DataType -> [(r, DataType)] -> Function r e
makeFunc name return args = Function name args return Seq.empty

pushBlock :: BasicBlock r e -> Function r e -> Function r e
pushBlock block = blocks %~ (:|> block)

functionValue :: Function r e -> Value r
functionValue func = ValFunction (FunctionT (func ^. retType) (map snd (func ^. args))) (func ^. funcId)

