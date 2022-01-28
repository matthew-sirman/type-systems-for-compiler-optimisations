{-# LANGUAGE TemplateHaskell #-}
module IR.BasicBlock where

import IR.Instructions

import Data.Sequence as Seq
import Control.Lens

data BasicBlock r = BasicBlock
    { _label :: Label
    , _iList :: Seq (Instruction r)
    }

makeLenses ''BasicBlock

instance Show r => Show (BasicBlock r) where
    show bb = show (bb ^. label) ++ ":\n" ++ concatMap (\i -> "    " ++ show i ++ "\n") (bb ^. iList)

makeBasicBlock :: Label -> BasicBlock r
makeBasicBlock l = BasicBlock l Seq.empty

blockPushFront, blockPush :: Instruction r -> BasicBlock r -> BasicBlock r
blockPushFront instruction = iList %~ (instruction :<|)
blockPush instruction = iList %~ (:|> instruction)

