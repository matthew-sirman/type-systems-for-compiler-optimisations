{-# LANGUAGE TemplateHaskell #-}
module IR.Program where

import IR.Instructions (FunctionID)
import IR.Function

import qualified Data.HashMap.Strict as M
import Control.Lens

newtype Program r = Program
    { _functions :: M.HashMap FunctionID (Function r)
    }

makeLenses ''Program

instance Show r => Show (Program r) where
    show program = concatMap show (M.elems (program ^. functions))

addFunction :: Function r -> Program r -> Program r
addFunction fn = functions %~ M.insert (fn ^. funcId) fn

