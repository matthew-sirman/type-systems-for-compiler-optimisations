{-# LANGUAGE TemplateHaskell #-}
module Compiler.Compiler where

import Parser.AST
import qualified Util.Stream as Stream

import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Program as IR

import qualified Data.HashMap.Strict as M
import Control.Monad.State
import Control.Lens

type Variable = Integer

data CompileState = CompileState
    { _blockStack :: [IR.BasicBlock Variable]
    , _funcStack :: [IR.Function Variable]
    , _compiledProgram :: IR.Program Variable
    , _labelIDs :: Stream.Stream Int
    , _functionNames :: Stream.Stream IR.FunctionID
    , _variableIDs :: Stream.Stream Variable
    }

makeLenses ''CompileState

compile :: ValExpr -> IR.Program Variable
compile expr = evalState finalise startState
    where
        finalise :: State CompileState (IR.Program Variable)
        finalise = do
            gets (^. compiledProgram)

        codegen :: ValExpr -> State CompileState (IR.Value Variable)
        codegen (VELet {}) = undefined
        codegen (VECase {}) = undefined
        codegen (VEApp {}) = undefined
        codegen (VELambda {}) = undefined
        codegen (VEVar {}) = undefined
        codegen (VELiteral {}) = undefined

        startState :: CompileState
        startState = CompileState 
            { _blockStack = []
            , _funcStack = []
            , _compiledProgram = IR.Program M.empty
            , _labelIDs = Stream.iterate (+1) 0
            , _functionNames = IR.FID "main" Stream.:> fmap (\f -> IR.FID ("__anonymous" ++ show f)) (Stream.iterate (+1) 0)
            , _variableIDs = Stream.iterate (+1) 0
            }

