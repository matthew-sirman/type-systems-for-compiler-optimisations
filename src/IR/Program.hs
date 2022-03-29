{-# LANGUAGE TemplateHaskell #-}
module IR.Program where

import IR.Instructions (FunctionID)
import IR.Function
import IR.DataType

import Data.Sequence as Seq
import Control.Lens

data Program r = Program
    { _functions :: [Function r]
    , _structs :: [Struct]
    }

makeLenses ''Program

instance Show r => Show (Program r) where
    show program = 
        concatMap show (program ^. structs) ++ "\n\n" ++
        concatMap show (program ^. functions)

emptyProgram :: Program r
emptyProgram = Program
    { _functions = []
    , _structs = []
    }

addFunction :: Function r -> Program r -> Program r
addFunction fn = functions %~ (fn:)

addStruct :: Struct -> Program r -> Program r
addStruct struct = structs %~ (struct:)

