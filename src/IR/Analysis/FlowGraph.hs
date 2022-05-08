{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module IR.Analysis.FlowGraph where

import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR

import Data.Sequence as Seq hiding (zip)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.Hashable (Hashable)
import Data.Foldable (toList)

import Control.Lens

import Debug.Trace

type NodeID = Int

data NodeType b
    = BlockNode b
    | EntryNode
    | ExitNode

instance Show b => Show (NodeType b) where
    show (BlockNode b) = show b
    show EntryNode = "Entry"
    show ExitNode = "Exit"

data Node b = Node
    { _node :: NodeType b
    , _inEdges :: S.HashSet NodeID
    , _outEdges :: S.HashSet NodeID
    }

makeLenses ''Node

instance Show b => Show (Node b) where
    show n = show (n ^. node) ++ "\n"
        ++ "In: " ++ show (toList (n ^. inEdges)) ++ "\n"
        ++ "Out: " ++ show (toList (n ^. outEdges)) ++ "\n\n"

data FlowGraph b = FlowGraph
    { _nodes :: M.HashMap NodeID (Node b)
    , _entryID :: NodeID
    , _exitID :: NodeID
    }
    
makeLenses ''FlowGraph

instance Show b => Show (FlowGraph b) where
    show graph = concatMap show (M.elems (graph ^. nodes)) ++ "\n\n"
        ++ "Entry: " ++ show (graph ^. entryID) ++ "\n"
        ++ "Exit: " ++ show (graph ^. exitID) ++ "\n"

type NodeIDMap = M.HashMap IR.Label NodeID

buildFlowGraph :: forall r e. IR.Function r e -> (FlowGraph (IR.BasicBlock r e), NodeIDMap)
buildFlowGraph fun =
    let graph = FlowGraph
            { _nodes = backwardPass
            , _entryID = entryNodeID
            , _exitID = exitNodeID
            }
     in (graph, blockNameMap)
    where
        blockNameMap :: NodeIDMap
        blockNameMap = M.fromList $ zip (toList (fmap (^. IR.label) (fun ^. IR.blocks))) [1..]

        entryNodeID, exitNodeID :: NodeID
        entryNodeID = 0
        exitNodeID = Seq.length (fun ^. IR.blocks) + 1

        entryNode, exitNode :: Node (IR.BasicBlock r e)
        entryNode = Node EntryNode S.empty (S.singleton 1)
        exitNode = Node ExitNode S.empty S.empty

        forwardPass :: M.HashMap NodeID (Node (IR.BasicBlock r e))
        forwardPass = pass (fun ^. IR.blocks) (M.fromList [(entryNodeID, entryNode), (exitNodeID, exitNode)])
            where
                pass :: Seq.Seq (IR.BasicBlock r e) -> M.HashMap NodeID (Node (IR.BasicBlock r e))
                     -> M.HashMap NodeID (Node (IR.BasicBlock r e))
                pass Seq.Empty = id
                pass (last :<| Seq.Empty) = M.insert (blockNameMap M.! (last ^. IR.label)) node
                    where
                        node :: Node (IR.BasicBlock r e)
                        node = addLinks exitNodeID last (Node (BlockNode last) S.empty S.empty)
                pass (blk :<| rest@(next :<| _)) = pass rest . M.insert (blockNameMap M.! (blk ^. IR.label)) node
                    where
                        node :: Node (IR.BasicBlock r e)
                        node = addLinks (blockNameMap M.! (next ^. IR.label)) blk (Node (BlockNode blk) S.empty S.empty)

                addLinks :: NodeID -> IR.BasicBlock r e -> Node (IR.BasicBlock r e)
                         -> Node (IR.BasicBlock r e)
                addLinks next bb = outEdges %~ updateLinks next (bb ^. IR.iList)
                
                updateLinks :: NodeID -> Seq (IR.Instruction r e) -> S.HashSet NodeID -> S.HashSet NodeID
                updateLinks _ (_ :|> IR.Jump lab) = S.insert (blockNameMap M.! lab)
                updateLinks next (_ :|> IR.Branch _ lab) = S.insert (blockNameMap M.! lab) . S.insert next
                updateLinks _ (_ :|> IR.Return _) = S.insert exitNodeID
                updateLinks next _ = S.insert next

        backwardPass :: M.HashMap NodeID (Node (IR.BasicBlock r e))
        backwardPass = M.foldlWithKey linkEdges forwardPass forwardPass
            where
                linkEdges :: M.HashMap NodeID (Node (IR.BasicBlock r e)) -> NodeID
                          -> Node (IR.BasicBlock r e)
                          -> M.HashMap NodeID (Node (IR.BasicBlock r e))
                linkEdges acc nid node = foldl (flip (M.adjust (addEdge nid))) acc (node ^. outEdges)

                addEdge :: NodeID -> Node b -> Node b
                addEdge target = inEdges %~ S.insert target

