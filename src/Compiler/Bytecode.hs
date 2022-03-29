{-# LANGUAGE TemplateHaskell #-}
module Compiler.Bytecode where

import Compiler.Compiler as C
import Compiler.RegisterAllocator as C
import qualified IR.Instructions as IR
import qualified IR.BasicBlock as IR
import qualified IR.Function as IR
import qualified IR.Program as IR
import qualified IR.Analysis.LiveVariableAnalysis as IR
import qualified IR.Analysis.FlowGraph as IR
import qualified IR.DataType as IR

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Sequence as Seq hiding (zip, replicate, reverse, length)
import Data.Array
import Data.Word
import Data.Foldable (toList)

import Control.Lens
import Control.Monad.State

-- TODO: Remove
import Debug.Trace

-- type BytecodeInstruction = IR.Instruction Int Int Int

data Register
    = Reg Word64
    | ReturnReg

instance Show Register where
    show (Reg r) = "r" ++ show r
    show ReturnReg = "ret_reg"

data BytecodeValue hole
    = Register Register
    | Immediate IR.Immediate
    | CodeLocation hole

instance Show hole => Show (BytecodeValue hole) where
    show (Register r) = show r
    show (Immediate imm) = show imm
    show (CodeLocation loc) = '$' : show loc

instance Functor BytecodeValue where
    fmap _ (Register r) = Register r
    fmap _ (Immediate imm) = Immediate imm
    fmap f (CodeLocation loc) = CodeLocation (f loc)

data BytecodeInstruction hole
    = Binop IR.BinaryOperator Register (BytecodeValue hole) (BytecodeValue hole)
    | Move Register (BytecodeValue hole)
    | Write (BytecodeValue hole) (BytecodeValue hole) Word64
    | Read Register (BytecodeValue hole) Word64
    | MAlloc Register (BytecodeValue hole)
    | Free (BytecodeValue hole)
    | Branch (BytecodeValue hole) hole
    | Jump hole
    | Call (BytecodeValue hole)
    | Return
    | Push (BytecodeValue hole)
    | Pop Register
    | Throw Int
    | CodeLabel hole

instance Show hole => Show (BytecodeInstruction hole) where
    show (Binop op res e1 e2) = show res ++ " = " ++ show op ++ " " ++ show e1 ++ ", " ++ show e2
    show (Move res e) = "mov " ++ show res ++ ", " ++ show e
    show (Write val addr size) = "wr " ++ show size ++ " " ++ show val ++ ", (" ++ show addr ++ ")"
    show (Read res loc size) = show res ++ " <- rd " ++ show size ++ " (" ++ show loc ++ ")"
    show (MAlloc res size) = show res ++ " = malloc " ++ show size
    show (Free ptr) = "free " ++ show ptr
    show (Branch val label) = "br " ++ show val ++ ", $" ++ show label
    show (Jump label) = "br $" ++ show label
    show (Call addr) = "call " ++ show addr
    show Return = "ret"
    show (Push val) = "push " ++ show val
    show (Pop reg) = "pop " ++ show reg
    show (Throw err) = "throw " ++ show err
    show (CodeLabel label) = show label ++ ":"

instance Functor BytecodeInstruction where
    fmap f (Binop op res e1 e2) = Binop op res (fmap f e1) (fmap f e2)
    fmap f (Move res e) = Move res (fmap f e)
    fmap f (Write val addr size) = Write (fmap f val) (fmap f addr) size
    fmap f (Read res loc size) = Read res (fmap f loc) size
    fmap f (MAlloc res size) = MAlloc res (fmap f size)
    fmap f (Free ptr) = Free (fmap f ptr)
    fmap f (Branch val label) = Branch (fmap f val) (f label)
    fmap f (Jump label) = Jump (f label)
    fmap f (Call addr) = Call (fmap f addr)
    fmap _ Return = Return
    fmap f (Push val) = Push (fmap f val)
    fmap _ (Pop reg) = Pop reg
    fmap _ (Throw err) = Throw err
    fmap f (CodeLabel label) = CodeLabel (f label)

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
            labelSize = fromIntegral $ length (show (len - 1))

            showI :: (Word64, BytecodeInstruction Word64) -> String
            showI (index, i) =
                replicate (fromIntegral labelSize - fromIntegral (length indexString)) ' '
                    ++ indexString ++ " " ++ show i ++ "\n"
                where
                    indexString = show index

data TargetHole
    = Fun IR.FunctionID
    | Block IR.Label

type Generator a = State GeneratorState a

data GeneratorState = GeneratorState
    { _phiRemaps :: M.HashMap IR.Label (C.Variable, C.Value)
    , _readTransforms :: M.HashMap C.Variable (Register -> Generator ())
    , _is :: Seq.Seq (BytecodeInstruction TargetHole)
    , _funcNameMap :: M.HashMap IR.FunctionID Word64
    , _blockLabelMap :: M.HashMap IR.Label Word64
    , _maxRegisters :: Word64
    }

makeLenses ''GeneratorState

generateBytecode :: C.Program -> Bytecode
generateBytecode compState = 
    let initState = GeneratorState
            { _phiRemaps = M.empty
            , _readTransforms = M.empty
            , _is = Seq.Empty
            , _funcNameMap = M.empty
            , _blockLabelMap = M.empty
            , _maxRegisters = 0
            }
        generate = do
            createPhiMap fns
            createInstructionList fns
            eraseLabels
        (emitted, gState) = runState generate initState
        instructionCount = fromIntegral (length emitted)
     in Bytecode
         { _instructions = listArray (0, instructionCount - 1) emitted
         , _bytecodeLength = instructionCount
         , _registerCount = fromIntegral (gState ^. maxRegisters)
         }
    where
        fns :: [C.Function]
        fns = compState ^. IR.functions

        createPhiMap :: [C.Function] -> Generator ()
        createPhiMap = mapM_ (mapM_ (mapM_ scanInstruction . (^. IR.iList)) . (^. IR.blocks))
            where
                scanInstruction :: C.Instruction -> Generator ()
                scanInstruction (IR.Phi target nodes) =
                    forM_ nodes $ \(IR.PhiNode (val, lab)) ->
                        modify (phiRemaps %~ M.insert lab (target, val))
                scanInstruction _ = pure ()

        createInstructionList :: [C.Function] -> Generator ()
        createInstructionList = mapM_ remapFunction

        remapFunction :: C.Function -> Generator ()
        remapFunction fn = do
            let (flowGraph, nodeIDMap) = IR.buildFlowGraph fn
                (_, liveVars) = IR.findLiveVarsDAG flowGraph
                clashGraph = IR.buildClashGraph liveVars
                registerAllocation = allocateRegisters clashGraph

            modify (maxRegisters %~ max (M.foldl max 0 registerAllocation + 1))

            pushI (pure (CodeLabel (Fun (fn ^. IR.funcId))))

            let argVars = map (Reg . (registerAllocation M.!)) (fn ^. IR.args)

            forM_ (reverse argVars) $ \arg ->
                pushI (pure (Pop arg))

            forM_ (fn ^. IR.blocks) $ \blk -> do
                let nodeID = nodeIDMap M.! (blk ^. IR.label)
                    lvaBB = ((liveVars ^. IR.nodes) M.! nodeID) ^. IR.node
                case lvaBB of
                  IR.BlockNode lvaBlock -> remapBlock registerAllocation lvaBlock blk
                  _ -> pure ()

        remapBlock :: M.HashMap Variable Word64 -> IR.LVABasicBlock Variable -> C.BasicBlock -> Generator ()
        remapBlock allocator lvaBlk blk = do
            pushI (pure (CodeLabel (Block (blk ^. IR.label))))

            sequence_ $ Seq.zipWith emit (lvaBlk ^. IR.lvaVars) (blk ^. IR.iList)
            
            phiMap <- gets (^. phiRemaps)
            case M.lookup (blk ^. IR.label) phiMap of
              Nothing -> pure ()
              Just (target, val) -> do
                  pushI (Move <$> remapVar target <*> remapV val)
                  swapWithJump
            where
                swapWithJump :: Generator ()
                swapWithJump = do
                    emitted <- gets (^. is)
                    case emitted of
                      entry :|> jump :|> move
                        | isJump jump -> modify (is .~ entry :|> move :|> jump)
                      _ -> pure ()

                isJump :: BytecodeInstruction a -> Bool
                isJump (Jump {}) = True
                isJump (Branch {}) = True
                isJump _ = False

                emit :: S.HashSet Variable -> C.Instruction -> Generator ()
                emit _ (IR.Binop op res e1 e2) =
                    pushI (Binop op <$> remapVar res <*> remapV e1 <*> remapV e2)
                emit _ (IR.Move res e) =
                    pushI (Move <$> remapVar res <*> remapV e)
                emit _ (IR.Write val addr dt) =
                    pushI (Write <$> remapV val <*> remapV addr <*> pure (IR.sizeof dt))
                emit _ (IR.Read res loc dt) = do
                    let readReg = remapVar res
                    pushI (Read <$> readReg <*> remapV loc <*> pure (IR.sizeof dt))
                    transform <- gets (M.lookup res . (^. readTransforms))
                    case (transform, readReg) of
                      (Just trans, Just reg) -> trans reg
                      _ -> pure ()
                emit _ inst@(IR.GetElementPtr res addr path) = do
                    offsetVal <- offset
                    pushI (Binop IR.Add <$> remapVar res <*> remapV addr <*> pure offsetVal)
                    where
                        offset :: Generator (BytecodeValue TargetHole)
                        offset = do
                            let IR.Pointer dt = IR.dataType addr
                                (byteOffset, bitOffset) = IR.elementPtrOffset dt path
                            when (bitOffset /= 0) $ do
                                let extractBit readReg = do
                                        let offset = Immediate (IR.Int64 (-bitOffset))
                                        pushI (Just (Binop IR.Shift readReg (Register readReg) offset))
                                modify (readTransforms %~ M.insert res extractBit)
                            pure (Immediate (IR.Int64 byteOffset))
                emit _ (IR.BitCast res e _) =
                    pushI (Move <$> remapVar res <*> remapV e)
                emit _ (IR.MAlloc res size) =
                    pushI (MAlloc <$> remapVar res <*> remapV size)
                emit _ (IR.Free ptr) =
                    pushI (Free <$> remapV ptr)
                emit lvs (IR.Call res func args) = do
                    let pushOrder = S.toList lvs

                    mapM_ pushVar pushOrder
                    mapM_ pushVal args
                    pushI (Call <$> remapV func)
                    mapM_ popVar (reverse pushOrder)
                    case res of
                      Nothing -> pure ()
                      Just r -> pushI (Move <$> remapVar r <*> pure (Register ReturnReg))
                    where
                        pushVal :: C.Value -> Generator ()
                        pushVal v = pushI (Push <$> remapV v)

                        pushVar :: Variable -> Generator ()
                        pushVar v = pushI (Push . Register <$> remapVar v)

                        popVar :: Variable -> Generator ()
                        popVar v = pushI (Pop <$> remapVar v)
                emit _ (IR.Branch val label) =
                    pushI (Branch <$> remapV val <*> pure (Block label))
                emit _ (IR.Jump label) =
                    pushI (pure (Jump (Block label)))
                emit _ (IR.Phi res ps) = pure () -- Phi (remapVar res) (fmap remapPhi ps)
                emit _ (IR.Return Nothing) = pushI (pure Return)
                emit _ (IR.Return (Just val)) = do
                    pushI (Move ReturnReg <$> remapV val)
                    pushI (pure Return)
                emit _ (IR.Throw err) = pushI (pure (Throw err))

                remapV :: C.Value -> Maybe (BytecodeValue TargetHole)
                remapV (IR.ValImmediate imm) = Just (Immediate imm)
                remapV (IR.ValVariable _ v) = Register <$> remapVar v
                remapV (IR.ValFunction _ name) = Just (CodeLocation (Fun name))
                remapV (IR.ValSizeOf dt) = Just (Immediate (IR.Int64 (IR.sizeof dt)))

                remapVar :: C.Variable -> Maybe Register
                remapVar var = Reg <$> M.lookup var allocator

        pushI :: Maybe (BytecodeInstruction TargetHole) -> Generator ()
        pushI Nothing = pure ()
        pushI (Just i) = modify (is %~ (:|> i))

eraseLabels :: Generator [BytecodeInstruction Word64]
eraseLabels = do
    labelled <- gets (^. is)
    withoutLabels <- findLabels 0 labelled
    fMap <- gets (^. funcNameMap)
    lMap <- gets (^. blockLabelMap)
    let remapTarget :: TargetHole -> Word64
        remapTarget (Fun fn) = fMap M.! fn
        remapTarget (Block blk) = lMap M.! blk
    pure (fmap (fmap remapTarget) withoutLabels)
    where
        findLabels :: Word64 -> Seq.Seq (BytecodeInstruction TargetHole)
                   -> Generator [BytecodeInstruction TargetHole]
        findLabels _ Seq.Empty = pure []
        findLabels count ((CodeLabel lab) :<| rest) = do
            case lab of
              Fun fn -> modify (funcNameMap %~ M.insert fn count)
              Block blk -> modify (blockLabelMap %~ M.insert blk count)
            findLabels count rest
        findLabels count (i :<| rest) = (i:) <$> findLabels (count + 1) rest

testEverything3 :: String -> Bytecode
testEverything3 = generateBytecode . testCompile

