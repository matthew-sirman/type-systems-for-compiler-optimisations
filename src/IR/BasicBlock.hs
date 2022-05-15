{-# LANGUAGE TemplateHaskell #-}
module IR.BasicBlock where

-- Basic Block data type

import IR.Instructions

import Data.Sequence as Seq
import Control.Lens

data BasicBlock r e = BasicBlock
    { _label :: Label
    , _iList :: Seq (Instruction r e)
    }

makeLenses ''BasicBlock

instance (Show e, Show r) => Show (BasicBlock r e) where
    show bb = show (bb ^. label) ++ ":\n" ++ concatMap (\i -> "    " ++ show i ++ "\n") (bb ^. iList)

makeBasicBlock :: Label -> BasicBlock r e
makeBasicBlock l = BasicBlock l Seq.empty

blockPushFront, blockPush :: Instruction r e -> BasicBlock r e -> BasicBlock r e
blockPushFront instruction = iList %~ (instruction :<|)
blockPush instruction = iList %~ (:|> instruction)

