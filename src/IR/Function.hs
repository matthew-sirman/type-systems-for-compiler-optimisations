{-# LANGUAGE TemplateHaskell #-}
module IR.Function where

import IR.Instructions
import IR.BasicBlock

import Data.Sequence as Seq
import Data.List (intercalate)
import Control.Lens

data Function r = Function
    { _funcId :: FunctionID
    , _args :: [r]
    , _blocks :: Seq (BasicBlock r)
    }

makeLenses ''Function

instance Show r => Show (Function r) where
    show fn = show (fn ^. funcId) ++ "(" ++ intercalate ", " (map show (fn ^. args)) ++ ") {\n" ++ concatMap show (fn ^. blocks) ++ "}\n\n"

makeFunc :: FunctionID -> [r] -> Function r
makeFunc name args = Function name args Seq.empty

pushBlock :: BasicBlock r -> Function r -> Function r
pushBlock block = blocks %~ (:|> block)

