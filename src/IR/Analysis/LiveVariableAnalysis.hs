{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module IR.Analysis.LiveVariableAnalysis where

import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Analysis.FlowGraph as IR

import Data.Sequence as Seq
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.List (intercalate)
import Data.Foldable (toList)
import Data.Hashable (Hashable)

import Control.Lens
import Control.Monad.State

data LVABasicBlock r = LVABasicBlock
    { _lvaBlockLabel :: IR.Label
    , _lvaVars :: Seq.Seq (S.HashSet r)
    }

makeLenses ''LVABasicBlock

instance Show r => Show (LVABasicBlock r) where
    show lvaBB =
        show (lvaBB ^. lvaBlockLabel) ++ ":\n"
            ++ concat (toList (fmap (\s -> "    " ++ showSet s ++ "\n") (lvaBB ^. lvaVars)))
        where
            showSet :: Show a => S.HashSet a -> String
            showSet s = "{" ++ intercalate ", " (map show $ toList s) ++ "}"

type Graph a = M.HashMap a (S.HashSet a)
type ClashGraph a = Graph a

ref :: (Eq r, Hashable r) => IR.Instruction r e -> S.HashSet r
ref (IR.Binop _ _ v1 v2) = valRef v1 `S.union` valRef v2
ref (IR.Move _ v) = valRef v
ref (IR.Write val addr _) = valRef val `S.union` valRef addr
ref (IR.Read _ addr _) = valRef addr
ref (IR.MAlloc _ size) = S.empty
ref (IR.GetElementPtr _ addr _) = valRef addr
ref (IR.BitCast _ val _) = valRef val
ref (IR.Free ptr) = valRef ptr
ref (IR.Call _ fun args) = valRef fun `S.union` S.unions (map valRef args)
ref (IR.Branch cond _) = valRef cond
ref (IR.Jump {}) = S.empty
-- TODO: This is currently over-conservatve. We only need to 
-- make variables live in the block they came from
ref (IR.Phi _ nodes) = S.unions (map (\(IR.PhiNode (val, _)) -> valRef val) nodes)
ref (IR.Return Nothing) = S.empty
ref (IR.Return (Just val)) = valRef val
ref (IR.Push val) = valRef val
ref (IR.Pop {}) = S.empty
ref (IR.PrintF _ args) = S.unions (map valRef args)
ref (IR.Throw {}) = S.empty
ref (IR.Comment {}) = S.empty

valRef :: Hashable r => IR.Value r -> S.HashSet r
valRef (IR.ValVariable _ r) = S.singleton r
valRef _ = S.empty

def :: (Eq r, Hashable r) => IR.Instruction r e -> S.HashSet r
def (IR.Binop _ res _ _) = S.singleton res
def (IR.Move res _) = S.singleton res
def (IR.Write {}) = S.empty
def (IR.Read res _ _) = S.singleton res
def (IR.GetElementPtr res _ _) = S.singleton res
def (IR.BitCast res _ _) = S.singleton res
def (IR.MAlloc res _) = S.singleton res
def (IR.Free {}) = S.empty
def (IR.Call Nothing _ _) = S.empty
def (IR.Call (Just res) _ _) = S.singleton res
def (IR.Branch {}) = S.empty
def (IR.Jump {}) = S.empty
def (IR.Phi res _) = S.singleton res
def (IR.Return {}) = S.empty
def (IR.Push {}) = S.empty
def (IR.Pop _ res) = S.singleton res
def (IR.PrintF {}) = S.empty
def (IR.Throw {}) = S.empty
def (IR.Comment {}) = S.empty

findBBLiveVars :: forall r e. (Eq r, Hashable r) => S.HashSet r -> IR.BasicBlock r e
               -> (LVABasicBlock r, S.HashSet r)
findBBLiveVars bbOutVars bb =
    let vars@(pred :<| _) = foldr combine (Seq.singleton bbOutVars) (bb ^. IR.iList)
        block = LVABasicBlock
            { _lvaBlockLabel = bb ^. IR.label
            , _lvaVars = vars
            }
     in (block, pred)
    where
        combine :: IR.Instruction r e -> Seq (S.HashSet r) -> Seq (S.HashSet r)
        combine i rest@(lvs :<| _) = ((lvs `S.difference` def i) `S.union` ref i) :<| rest

data LVAState r = LVAState
    { _memoMap :: M.HashMap IR.NodeID (S.HashSet r)
    , _lvaGraph :: IR.FlowGraph (LVABasicBlock r)
    }

makeLenses ''LVAState

findLiveVarsDAG :: forall r e. (Eq r, Hashable r) => IR.FlowGraph (IR.BasicBlock r e)
                -> (S.HashSet r, IR.FlowGraph (LVABasicBlock r))
findLiveVarsDAG flowGraph =
    let entry = flowGraph ^. IR.entryID
        exit = flowGraph ^. IR.exitID

        initState = LVAState
            { _memoMap = M.empty
            , _lvaGraph = IR.FlowGraph
                { IR._nodes = M.empty
                , IR._entryID = entry
                , IR._exitID = exit
                }
            }
        (fvs, s) = runState (calcLVs entry (getNode entry)) initState
     in (fvs, s ^. lvaGraph)
    where
        getNode :: IR.NodeID -> IR.Node (IR.BasicBlock r e)
        getNode = ((flowGraph ^. IR.nodes) M.!)

        calcLVs :: IR.NodeID -> IR.Node (IR.BasicBlock r e) -> State (LVAState r) (S.HashSet r)
        calcLVs _ (IR.Node IR.ExitNode is os) = do
            modify (lvaGraph . IR.nodes %~ M.insert (flowGraph ^. IR.exitID) (IR.Node IR.ExitNode is os))
            pure S.empty

        calcLVs _ (IR.Node IR.EntryNode is os) = do
            modify (lvaGraph . IR.nodes %~ M.insert (flowGraph ^. IR.entryID) (IR.Node IR.EntryNode is os))
            combineSuccessors os

        calcLVs nid (IR.Node (IR.BlockNode bb) is os) = do
            memo <- gets (^. memoMap)
            case M.lookup nid memo of
              Just s -> pure s
              Nothing -> do
                  succs <- combineSuccessors os
                  let (newBB, predSet) = findBBLiveVars succs bb
                  modify ( (memoMap %~ M.insert nid predSet)
                         . (lvaGraph . IR.nodes %~ M.insert nid (IR.Node (IR.BlockNode newBB) is os))
                         )
                  pure predSet
        
        combineSuccessors :: S.HashSet IR.NodeID -> State (LVAState r) (S.HashSet r)
        combineSuccessors = foldM combine S.empty
            where
                combine :: S.HashSet r -> IR.NodeID -> State (LVAState r) (S.HashSet r)
                combine s n = flip S.union s <$> calcLVs n (getNode n)

buildClashGraph :: forall r. (Eq r, Hashable r) => IR.FlowGraph (LVABasicBlock r) -> ClashGraph r
buildClashGraph graph = foldr (M.unionWith S.union . findBBClashes) M.empty (M.elems (graph ^. IR.nodes))
    where
        findBBClashes :: IR.Node (LVABasicBlock r) -> ClashGraph r
        findBBClashes (IR.Node (IR.BlockNode bb) _ _) = foldr addClashes M.empty (bb ^. lvaVars)
        findBBClashes _ = M.empty

        addClashes :: S.HashSet r -> ClashGraph r -> ClashGraph r
        addClashes s g = foldr (\element -> M.insertWith S.union element (S.delete element s)) g s

