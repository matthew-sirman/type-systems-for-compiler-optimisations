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
import Data.List (intercalate)

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
    | Free (BytecodeValue hole) Word64
    | Branch (BytecodeValue hole) hole
    | Jump hole
    | Call (BytecodeValue hole)
    | Return
    | Push (BytecodeValue hole)
    | Pop (Maybe Register)
    | Save (BytecodeValue hole)
    | Restore Register
    | PrintF String [BytecodeValue hole]
    | Throw C.ReturnStatus
    | StaticAlloc Word64 Word64
    | CodeLabel hole

instance Show hole => Show (BytecodeInstruction hole) where
    show (Binop op res e1 e2) = show res ++ " = " ++ show op ++ " " ++ show e1 ++ ", " ++ show e2
    show (Move res e) = "mov " ++ show res ++ ", " ++ show e
    show (Write val addr size) = "wr [" ++ show size ++ "] " ++ show val ++ ", (" ++ show addr ++ ")"
    show (Read res loc size) = show res ++ " <- rd [" ++ show size ++ "] (" ++ show loc ++ ")"
    show (MAlloc res size) = show res ++ " = malloc " ++ show size
    show (Free ptr size) = "free [" ++ show size ++ "] " ++ show ptr
    show (Branch val label) = "br " ++ show val ++ ", $" ++ show label
    show (Jump label) = "br $" ++ show label
    show (Call addr) = "call " ++ show addr
    show Return = "ret"
    show (Push val) = "push " ++ show val
    show (Pop Nothing) = "pop"
    show (Pop (Just reg)) = "pop " ++ show reg
    show (Save val) = "save " ++ show val
    show (Restore reg) = "restore " ++ show reg
    show (PrintF fmt []) = "printf(" ++ show fmt ++ ")"
    show (PrintF fmt args) = "printf(" ++ show fmt ++ ", " ++ intercalate ", " (map show args) ++ ")"
    show (Throw err) = "throw " ++ show err
    show (StaticAlloc base size) = "alloc [" ++ show base ++ "-" ++ show (base + size) ++ "]"
    show (CodeLabel label) = show label ++ ":"

instance Functor BytecodeInstruction where
    fmap f (Binop op res e1 e2) = Binop op res (fmap f e1) (fmap f e2)
    fmap f (Move res e) = Move res (fmap f e)
    fmap f (Write val addr size) = Write (fmap f val) (fmap f addr) size
    fmap f (Read res loc size) = Read res (fmap f loc) size
    fmap f (MAlloc res size) = MAlloc res (fmap f size)
    fmap f (Free ptr size) = Free (fmap f ptr) size
    fmap f (Branch val label) = Branch (fmap f val) (f label)
    fmap f (Jump label) = Jump (f label)
    fmap f (Call addr) = Call (fmap f addr)
    fmap _ Return = Return
    fmap f (Push val) = Push (fmap f val)
    fmap _ (Pop reg) = Pop reg
    fmap f (Save val) = Save (fmap f val)
    fmap _ (Restore reg) = Restore reg
    fmap f (PrintF fmt args) = PrintF fmt (fmap f <$> args)
    fmap _ (Throw err) = Throw err
    fmap _ (StaticAlloc base size) = StaticAlloc base size
    fmap f (CodeLabel label) = CodeLabel (f label)

data TargetHole
    = Fun IR.FunctionID
    | Block IR.Label

instance Show TargetHole where
    show (Fun fid) = "<fun> " ++ show fid
    show (Block bid) = "<blk> " ++ show bid

data Bytecode = Bytecode
    { _instructions :: Array Word64 (Maybe TargetHole, BytecodeInstruction Word64)
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

            showI :: (Word64, (Maybe TargetHole, BytecodeInstruction Word64)) -> String
            showI (index, (label, i)) =
                prefix
                    ++ replicate (4 + fromIntegral labelSize - fromIntegral (length indexString)) ' '
                    ++ indexString ++ " " ++ show i ++ "\n"
                where
                    prefix :: String
                    prefix = case label of
                               Nothing -> ""
                               Just l -> show l ++ ":\n"
                    indexString = show index

type Generator a = State GeneratorState a

data GeneratorState = GeneratorState
    { _phiRemaps :: M.HashMap IR.Label (C.Variable, C.Value)
    , _readTransforms :: M.HashMap C.Variable (Register -> Generator ())
    , _is :: Seq.Seq (BytecodeInstruction TargetHole)
    , _funcNameMap :: M.HashMap IR.FunctionID Word64
    , _blockLabelMap :: M.HashMap IR.Label Word64
    , _maxRegisters :: Word64
    , _staticAllocation :: Word64
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
            , _staticAllocation = 0
            }
        generate = do
            createPhiMap fns
            createInstructionList
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

        createInstructionList :: Generator ()
        createInstructionList = do
            staticMap <- M.fromList <$> mapM generateStaticAllocation (compState ^. IR.globals)
            mapM_ (generateFunction staticMap) fns

        generateStaticAllocation :: IR.GlobalBlock Variable -> Generator (String, BytecodeValue TargetHole)
        generateStaticAllocation global = do
            staticBlockPtr <- gets (^. staticAllocation)

            let totalSize = IR.sizeof (IR.Structure (map IR.datatype (global ^. IR.blockData)))
            pushI (Just (StaticAlloc staticBlockPtr totalSize))

            forM_ (global ^. IR.blockData) $ \val -> do
                valuePtr <- gets (^. staticAllocation)
                let size = IR.sizeof (IR.datatype val)
                case globalVal val of
                  Just v -> pushI (Just (Write v (Immediate (IR.Int64 (fromIntegral valuePtr))) size))
                  Nothing -> pushI (Just (Throw StaticAllocationDependence))
                modify (staticAllocation %~ (+size))

            pure (global ^. IR.globalName, Immediate (IR.Int64 (fromIntegral staticBlockPtr)))
            where
                globalVal :: C.Value -> Maybe (BytecodeValue TargetHole)
                globalVal (IR.ValImmediate imm) = Just (Immediate imm)
                globalVal (IR.ValVariable _ v) = Nothing
                globalVal (IR.ValGlobal global) = Nothing
                globalVal (IR.ValFunction _ name) = Just (CodeLocation (Fun name))
                globalVal (IR.ValSizeOf dt) = Just (Immediate (IR.Int64 (IR.sizeof dt)))

        generateFunction :: M.HashMap String (BytecodeValue TargetHole) -> C.Function -> Generator ()
        generateFunction staticMap fn = do
            let (flowGraph, nodeIDMap) = IR.buildFlowGraph fn
                (_, liveVars) = IR.findLiveVarsDAG flowGraph
                clashGraph = IR.buildClashGraph liveVars
                registerAllocation = allocateRegisters clashGraph

            modify (maxRegisters %~ max (M.foldl max 0 registerAllocation + 1))

            pushI (pure (CodeLabel (Fun (fn ^. IR.funcId))))

            let argVars = map ((Reg <$>) . (`M.lookup` registerAllocation) . fst) (fn ^. IR.args)

            forM_ (reverse argVars) $ \arg ->
                pushI (pure (Pop arg))

            forM_ (fn ^. IR.blocks) $ \blk -> do
                let nodeID = nodeIDMap M.! (blk ^. IR.label)
                    lvaBB = (^. IR.node) <$> M.lookup nodeID (liveVars ^. IR.nodes)
                case lvaBB of
                  Just (IR.BlockNode lvaBlock) -> generateBlock staticMap registerAllocation lvaBlock blk
                  _ -> pure ()

        generateBlock :: M.HashMap String (BytecodeValue TargetHole) -> M.HashMap Variable Word64
                      -> IR.LVABasicBlock Variable -> C.BasicBlock
                      -> Generator ()
        generateBlock staticMap allocator lvaBlk blk = do
            pushI (pure (CodeLabel (Block (blk ^. IR.label))))

            sequence_ $ Seq.zipWith emit (lvaBlk ^. IR.lvaVars) (blk ^. IR.iList)
            
            phiMap <- gets (^. phiRemaps)
            case M.lookup (blk ^. IR.label) phiMap of
              Nothing -> pure ()
              Just (target, val) -> do
                  pushI (Move <$> generateVar target <*> generateVal val)
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
                    pushI (Binop op <$> generateVar res <*> generateVal e1 <*> generateVal e2)
                emit _ (IR.Move res e) =
                    pushI (Move <$> generateVar res <*> generateVal e)
                emit _ (IR.Write val addr dt) =
                    pushI (Write <$> generateVal val <*> generateVal addr <*> pure (IR.sizeof dt))
                emit _ (IR.Read res loc dt) = do
                    let readReg = generateVar res
                    pushI (Read <$> readReg <*> generateVal loc <*> pure (IR.sizeof dt))
                    transform <- gets (M.lookup res . (^. readTransforms))
                    case (transform, readReg) of
                      (Just trans, Just reg) -> trans reg
                      _ -> pure ()
                emit _ inst@(IR.GetElementPtr res addr path) = do
                    offsetVal <- offset
                    pushI (Binop IR.Add <$> generateVar res <*> generateVal addr <*> pure offsetVal)
                    where
                        offset :: Generator (BytecodeValue TargetHole)
                        offset = do
                            let IR.Pointer dt = IR.datatype addr
                                (byteOffset, bitOffset) = IR.elementPtrOffset dt path
                            when (bitOffset /= 0) $ do
                                let extractBit readReg = do
                                        let offset = Immediate (IR.Int64 (-bitOffset))
                                        pushI (Just (Binop IR.Shift readReg (Register readReg) offset))
                                modify (readTransforms %~ M.insert res extractBit)
                            pure (Immediate (IR.Int64 byteOffset))
                emit _ (IR.BitCast res e _) =
                    pushI (Move <$> generateVar res <*> generateVal e)
                emit _ (IR.MAlloc res size) =
                    pushI (MAlloc <$> generateVar res <*> generateVal size)
                emit _ (IR.Free ptr) =
                    let IR.Pointer baseType = IR.datatype ptr
                     in pushI (Free <$> generateVal ptr <*> pure (IR.sizeof baseType))
                emit lvs (IR.Call res func args) = do
                    let pushOrder = S.toList lvs

                    mapM_ saveVar pushOrder
                    mapM_ pushVal args
                    pushI (Call <$> generateVal func)
                    mapM_ restoreVar (reverse pushOrder)
                    case res of
                      Nothing -> pure ()
                      Just r -> pushI (Move <$> generateVar r <*> pure (Register ReturnReg))
                    where
                        pushVal :: C.Value -> Generator ()
                        pushVal v = pushI (Push <$> generateVal v)

                        saveVar :: Variable -> Generator ()
                        saveVar v = pushI (Save . Register <$> generateVar v)

                        restoreVar :: Variable -> Generator ()
                        restoreVar v = pushI (Restore <$> generateVar v)
                emit _ (IR.Branch val label) =
                    pushI (Branch <$> generateVal val <*> pure (Block label))
                emit _ (IR.Jump label) =
                    pushI (pure (Jump (Block label)))
                emit _ (IR.Phi res ps) = pure () -- Phi (generateVar res) (fmap generatePhi ps)
                emit _ (IR.Return Nothing) = pushI (pure Return)
                emit _ (IR.Return (Just val)) = do
                    pushI (Move ReturnReg <$> generateVal val)
                    pushI (pure Return)
                emit _ (IR.Push val) = pushI (Push <$> generateVal val)
                emit _ (IR.Pop _ res) = pushI (Just (Pop (generateVar res)))
                emit _ (IR.PrintF fmt args) = do
                    pushI (PrintF fmt <$> mapM generateVal args)
                emit _ (IR.Throw err) = pushI (pure (Throw err))
                emit _ (IR.Comment {}) = pure ()

                generateVal :: C.Value -> Maybe (BytecodeValue TargetHole)
                generateVal (IR.ValImmediate imm) = Just (Immediate imm)
                generateVal (IR.ValVariable _ v) = Register <$> generateVar v
                generateVal (IR.ValGlobal global) = M.lookup (global ^. IR.globalName) staticMap
                generateVal (IR.ValFunction _ name) = Just (CodeLocation (Fun name))
                generateVal (IR.ValSizeOf dt) = Just (Immediate (IR.Int64 (IR.sizeof dt)))

                generateVar :: C.Variable -> Maybe Register
                generateVar var = Reg <$> M.lookup var allocator

        pushI :: Maybe (BytecodeInstruction TargetHole) -> Generator ()
        pushI Nothing = pure ()
        pushI (Just i) = modify (is %~ (:|> i))

eraseLabels :: Generator [(Maybe TargetHole, BytecodeInstruction Word64)]
eraseLabels = do
    labelled <- gets (^. is)
    withoutLabels <- findLabels 0 labelled
    fMap <- gets (^. funcNameMap)
    lMap <- gets (^. blockLabelMap)
    let remapTarget :: TargetHole -> Word64
        remapTarget (Fun fn) = fMap M.! fn
        remapTarget (Block blk) = lMap M.! blk
    pure (fmap (fmap (fmap remapTarget)) withoutLabels)
    where
        findLabels :: Word64 -> Seq.Seq (BytecodeInstruction TargetHole)
                   -> Generator [(Maybe TargetHole, BytecodeInstruction TargetHole)]
        findLabels _ Seq.Empty = pure []
        findLabels count ((CodeLabel lab) :<| rest) = do
            case lab of
              Fun fn -> modify (funcNameMap %~ M.insert fn count)
              Block blk -> modify (blockLabelMap %~ M.insert blk count)
            updateHeadLabel lab <$> findLabels count rest
        findLabels count (i :<| rest) = ((Nothing, i):) <$> findLabels (count + 1) rest

        updateHeadLabel :: TargetHole -> [(Maybe TargetHole, BytecodeInstruction TargetHole)]
                        -> [(Maybe TargetHole, BytecodeInstruction TargetHole)]
        updateHeadLabel _ [] = []
        updateHeadLabel l ((_, i):is) = (Just l, i) : is

testEverything3 :: String -> Bytecode
testEverything3 = generateBytecode . testCompile

