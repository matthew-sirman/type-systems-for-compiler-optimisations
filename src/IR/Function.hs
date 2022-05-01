{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module IR.Function where

import IR.Instructions
import IR.BasicBlock
import IR.DataType

import Data.Sequence as Seq
import Data.List (intercalate)
import Control.Lens

data Function r = Function
    { _funcId :: FunctionID
    , _args :: [(r, DataType)]
    , _retType :: DataType
    , _blocks :: Seq (BasicBlock r)
    }

makeLenses ''Function

instance Show r => Show (Function r) where
    show fn = show (fn ^. retType) ++ " " ++ show (fn ^. funcId)
            ++ "(" ++ intercalate ", " (map showArg (fn ^. args)) ++ ") {\n" ++ concatMap show (fn ^. blocks) ++ "}\n\n"
        where
            showArg :: (r, DataType) -> String
            showArg (v, t) = show v ++ " : " ++ show t

makeFunc :: FunctionID -> DataType -> [(r, DataType)] -> Function r
makeFunc name return args = Function name args return Seq.empty

pushBlock :: BasicBlock r -> Function r -> Function r
pushBlock block = blocks %~ (:|> block)

functionValue :: Function r -> Value r
functionValue func = ValFunction (FunctionT (func ^. retType) (map snd (func ^. args))) (func ^. funcId)

