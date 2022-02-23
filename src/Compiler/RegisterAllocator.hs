{-# LANGUAGE ScopedTypeVariables #-}
module Compiler.RegisterAllocator where

import qualified IR.BasicBlock as IR

import qualified IR.Analysis.FlowGraph as IR
import qualified IR.Analysis.LiveVariableAnalysis as IR
import Compiler.Compiler

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Word
import Data.Hashable (Hashable)

import Control.Monad.State

allocateRegisters :: IR.ClashGraph Variable -> M.HashMap Variable Word64
allocateRegisters cGraph = allocate allocStack M.empty
    where
        allocStack :: [Variable]
        allocStack = evalState createStack cGraph

        allocate :: [Variable] -> M.HashMap Variable Word64 -> M.HashMap Variable Word64
        allocate [] acc = acc
        allocate (v:vs) acc = allocate vs (M.insert v (findNext 0) acc)
            where
                findNext :: Word64 -> Word64
                findNext reg
                    | neighbours reg = findNext (reg + 1)
                    | otherwise = reg

                neighbours :: Word64 -> Bool
                neighbours reg = any (isNeighbour reg) (cGraph M.! v)

                isNeighbour :: Word64 -> Variable -> Bool
                isNeighbour reg var =
                    case M.lookup var acc of
                      Just reg'
                        | reg == reg' -> True
                      _ -> False


        createStack :: State (IR.ClashGraph Variable) [Variable]
        createStack = do
            minVertex <- popMinVertex
            case minVertex of
              Nothing -> pure []
              Just next -> (next:) <$> createStack

        popMinVertex :: State (IR.ClashGraph Variable) (Maybe Variable)
        popMinVertex = do
            graph <- get
            let minVertex = fst <$> M.foldlWithKey findMin Nothing graph
            modify (popNode minVertex)
            pure minVertex
            where
                findMin :: Maybe (Variable, Int) -> Variable -> S.HashSet Variable -> Maybe (Variable, Int)
                findMin Nothing v es = Just (v, S.size es)
                findMin (Just (v, best)) v' es
                    | eSize < best = Just (v', eSize)
                    | otherwise = Just (v, best)
                    where
                        eSize :: Int
                        eSize = S.size es

                popNode :: Maybe Variable -> IR.ClashGraph Variable -> IR.ClashGraph Variable
                popNode Nothing = id
                popNode (Just v) = M.map (S.delete v) . M.delete v


