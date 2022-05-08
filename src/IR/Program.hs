{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module IR.Program where

import IR.Instructions (FunctionID, GlobalBlock)
import IR.Function
import IR.DataType

import Data.Sequence as Seq
import Data.List (intercalate)
import Control.Lens

data Program r e = Program
    { _functions :: [Function r e]
    , _structs :: [Struct]
    , _globals :: [GlobalBlock r]
    }

makeLenses ''Program

instance (Show r, Show e) => Show (Program r e) where
    show program = 
        concatMap show (program ^. structs) ++ "\n\n" ++
        concatMap show (program ^. globals) ++ "\n\n" ++
        concatMap show (program ^. functions)

emptyProgram :: Program r e
emptyProgram = Program
    { _functions = []
    , _structs = []
    , _globals = []
    }

addFunction :: Function r e -> Program r e -> Program r e
addFunction fn = functions %~ (fn:)

addStruct :: Struct -> Program r e -> Program r e
addStruct struct = structs %~ (struct:)

addGlobal :: GlobalBlock r -> Program r e -> Program r e
addGlobal global = globals %~ (global:)

