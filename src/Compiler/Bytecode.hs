{-# LANGUAGE TemplateHaskell #-}
module Compiler.Bytecode where

import Compiler.Compiler as C
import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Program as IR

import qualified Data.HashMap.Strict as M
import Data.Sequence as Seq hiding (zip, replicate)
import Data.Array
import Data.Word
import Data.Foldable (toList)

import Control.Lens
import Control.Monad.State

-- type BytecodeInstruction = IR.Instruction Int Int Int

data Register
    = Reg Word64
    | ReturnReg

instance Show Register where
    show (Reg r) = "r" ++ show r
    show ReturnReg = "ret_reg"

data BytecodeValue
    = Register Register
    | Immediate IR.Immediate
instance Show BytecodeValue where
    show (Register r) = show r
    show (Immediate imm) = show imm

data CallTarget hole
    = Direct hole
    | Indirect BytecodeValue

instance Show hole => Show (CallTarget hole) where
    show (Direct addr) = show addr
    show (Indirect val) = show val

data BytecodeInstruction hole
    = Binop IR.BinaryOperator Register BytecodeValue BytecodeValue
    | Move Register BytecodeValue
    | Write BytecodeValue BytecodeValue Word64
    | Read Register BytecodeValue Word64
    | MAlloc Register BytecodeValue
    | Branch BytecodeValue hole
    | Jump hole
    | Call (CallTarget hole)
    | Return
    | Push BytecodeValue
    | Pop Register
    | Throw Int

instance Show hole => Show (BytecodeInstruction hole) where
    show (Binop op res e1 e2) = show res ++ " = " ++ show op ++ " " ++ show e1 ++ ", " ++ show e2
    show (Move res e) = "mov " ++ show res ++ ", " ++ show e
    show (Write val addr size) = "wr " ++ show size ++ " " ++ show val ++ ", (" ++ show addr ++ ")"
    show (Read res loc size) = show res ++ " <- rd " ++ show size ++ " (" ++ show loc ++ ")"
    show (MAlloc res size) = show res ++ " = malloc " ++ show size
    show (Branch val label) = "br " ++ show val ++ ", " ++ show label
    show (Jump label) = "br " ++ show label
    show (Call addr) = "call " ++ show addr
    show Return = "ret"
    show (Throw err) = "throw " ++ show err

data Bytecode = Bytecode
    { _instructions :: Array Word64 (BytecodeInstruction Word64)
    , _bytecodeLength :: Word64
    , _registerCount :: Word64
    }

makeLenses ''Bytecode

instance Show Bytecode where
    show b = "Program length: " ++ show (b ^. bytecodeLength) ++ " instructions.\n\n"
            ++ concatMap showI (assocs (b ^. instructions))
        where
            len :: Word64
            len = b ^. bytecodeLength

            labelSize :: Word64
            labelSize = fromIntegral $ Prelude.length (show (len - 1))

            showI :: (Word64, BytecodeInstruction Word64) -> String
            showI (index, i) =
                replicate (fromIntegral labelSize - fromIntegral (Prelude.length indexString)) ' '
                    ++ indexString ++ " " ++ show i ++ "\n"
                where
                    indexString = show index

data TargetHole
    = Fun IR.FunctionID
    | Block IR.Label

data GeneratorState = GeneratorState
    { _funcNameMap :: M.HashMap IR.FunctionID Word64
    , _blockLabelMap :: M.HashMap IR.Label Word64
    , _iCount :: Word64
    }

makeLenses ''GeneratorState

type Generator a = State GeneratorState a

generateBytecode :: CompileState -> Bytecode
generateBytecode compState = 
    let initState = GeneratorState
            { _funcNameMap = M.empty
            , _blockLabelMap = M.empty
            , _iCount = 0
            }
        (is, gs) = runState (createInstructionList fns) initState
     in Bytecode
           { _instructions = listArray (0, gs ^. iCount - 1) (remapLabels gs is)
            , _bytecodeLength = gs ^. iCount
            , _registerCount = fromIntegral (compState ^. variableID)
            }
    where
        fns :: [C.Function]
        fns = compState ^. compiledProgram . IR.functions

        -- TODO: Maybe reformulate this as a traversal?
        createInstructionList :: [C.Function] -> Generator [BytecodeInstruction TargetHole]
        createInstructionList [] = pure []
        createInstructionList (fn:fns) = do
            fnIndex <- gets (^. iCount)
            modify (funcNameMap %~ M.insert (fn ^. IR.funcId) fnIndex)

            let entry = [Move (remapVar r) (Register (ArgReg i)) | (r, i) <- zip (fn ^. IR.args) [0..]] 
                addedEntry = fromIntegral (Prelude.length entry)
            modify (iCount %~ (+addedEntry))
            funCode <- (entry ++) <$> remapBlocks (fn ^. IR.blocks)
            rest <- createInstructionList fns
            pure (funCode ++ rest)

        remapBlocks :: Seq C.BasicBlock -> Generator [BytecodeInstruction TargetHole]
        remapBlocks Seq.Empty = pure []
        remapBlocks (blk :<| blks) = do
            blkIndex <- gets (^. iCount)
            modify (blockLabelMap %~ M.insert (blk ^. IR.label) blkIndex)

            let blockCode = concat (toList (fmap remapI (blk ^. IR.iList)))
                addedIs = fromIntegral (Prelude.length blockCode)
            modify (iCount %~ (+addedIs))
            rest <- remapBlocks blks
            pure (blockCode ++ rest)

        remapI :: C.Instruction -> [BytecodeInstruction TargetHole]
        remapI (IR.Binop op res e1 e2) = [Binop op (remapVar res) (remapV e1) (remapV e2)]
        remapI (IR.Move res e) = [Move (remapVar res) (remapV e)]
        remapI (IR.Write val addr size) = [Write (remapV val) (remapV addr) size]
        remapI (IR.Read res loc size) = [Read (remapVar res) (remapV loc) size]
        remapI (IR.MAlloc res size) = [MAlloc (remapVar res) (remapV size)]
        remapI (IR.Call res func args) = movArgs 0 args
            where
                movArgs :: Word64 -> [C.Value] -> [BytecodeInstruction TargetHole]
                movArgs _ [] = call
                movArgs a (v:vs) = Move (ArgReg a) (remapV v) : movArgs (a + 1) vs
                
                callTarget :: CallTarget TargetHole
                callTarget = case func of
                               IR.ValClosure (IR.Closure name _) -> Direct (Fun name)
                               _ -> Indirect (remapV func)

                call :: [BytecodeInstruction TargetHole]
                call = case res of
                         Nothing -> [Call callTarget]
                         Just r -> [Call callTarget, Move (remapVar r) (Register ReturnReg)]
        remapI (IR.Branch val label) = [Branch (remapV val) (Block label)]
        remapI (IR.Jump label) = [Jump (Block label)]
        remapI (IR.Phi res ps) = undefined -- Phi (remapVar res) (fmap remapPhi ps)
        remapI (IR.Return Nothing) = [Return]
        remapI (IR.Return (Just val)) = [Move ReturnReg (remapV val), Return]
        remapI (IR.Throw err) = [Throw err]

        remapV :: C.Value -> BytecodeValue
        remapV (IR.ValImmediate imm) = Immediate imm
        remapV (IR.ValVariable v) = Register (remapVar v)
        remapV (IR.ValClosure (IR.Closure name (Just cl))) = Register (remapVar cl)

        remapVar :: C.Variable -> Register
        remapVar (C.Strict v) = Reg (fromIntegral v)
        remapVar (C.Lazy v _ _ _) = Reg (fromIntegral v)
        remapVar (C.Argument v) = Reg (fromIntegral v)

        remapLabels :: GeneratorState -> [BytecodeInstruction TargetHole] -> [BytecodeInstruction Word64]
        remapLabels gs = map remap
            where
                remap :: BytecodeInstruction TargetHole -> BytecodeInstruction Word64
                remap (Binop op r v1 v2) = Binop op r v1 v2
                remap (Move r v) = Move r v
                remap (Write v addr size) = Write v addr size
                remap (Read r v size) = Read r v size
                remap (MAlloc r size) = MAlloc r size
                remap (Branch v target) =  Branch v (remapTarget target)
                remap (Jump target) = Jump (remapTarget target)
                remap (Call (Direct target)) = Call (Direct (remapTarget target))
                remap (Call (Indirect target)) = Call (Indirect target)
                remap Return = Return
                remap (Throw err) = Throw err

                remapTarget :: TargetHole -> Word64
                remapTarget (Fun fn) = fMap M.! fn
                remapTarget (Block blk) = lMap M.! blk

                fMap :: M.HashMap IR.FunctionID Word64
                fMap = gs ^. funcNameMap

                lMap :: M.HashMap IR.Label Word64
                lMap = gs ^. blockLabelMap

