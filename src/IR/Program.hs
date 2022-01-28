{-# LANGUAGE TemplateHaskell #-}
module IR.Program where

import IR.Instructions (FunctionID)
import IR.Function

import Data.Sequence as Seq
import Control.Lens

newtype Program r = Program
    { _functions :: [Function r]
    }

makeLenses ''Program

instance Show r => Show (Program r) where
    show program = concatMap show (program ^. functions)

addFunction :: Function r -> Program r -> Program r
addFunction fn = functions %~ (fn:)

