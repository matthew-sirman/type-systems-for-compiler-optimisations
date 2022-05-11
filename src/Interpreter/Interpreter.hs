{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module Interpreter.Interpreter where

import IR.Instructions (BinaryOperator(..), Immediate(..))

import Compiler.Bytecode
import Compiler.Compiler (ReturnStatus(..))

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Lens

import Data.Array
import Data.Array.IO
import Data.Word
import Data.Bits

import Text.Printf

-- TODO: Remove
import Debug.Trace

data ProgramStats = ProgramStats
    { _staticMemoryAllocation :: Word64
    , _dynamicMemoryAllocation :: Word64
    , _reclaimedMemory :: Word64
    , _maximumMemory :: Word64
    , _instructionsExecuted :: Word64
    , _readsExecuted :: Word64
    , _writesExecuted :: Word64
    }

makeLenses ''ProgramStats

instance Show ProgramStats where
    show stats =
        "Static memory allocated: " ++ show (stats ^. staticMemoryAllocation) ++ "\n" ++
        "Dynamic memory allocated: " ++ show (stats ^. dynamicMemoryAllocation) ++ "\n" ++
        "Memory deallocated: " ++ show (stats ^. reclaimedMemory) ++ "\n" ++
        "Maximum dynamic memory held: " ++ show (stats ^. maximumMemory) ++ "\n" ++
        "Instructions executed: " ++ show (stats ^. instructionsExecuted) ++ "\n" ++
        "Reads executed: " ++ show (stats ^. readsExecuted) ++ "\n" ++
        "Writes executed: " ++ show (stats ^. writesExecuted) ++ "\n"

showStatsCsv :: ProgramStats -> String
showStatsCsv stats = show (stats ^. staticMemoryAllocation) ++ ", " ++
                     show (stats ^. dynamicMemoryAllocation) ++ ", " ++
                     show (stats ^. reclaimedMemory) ++ ", " ++
                     show (stats ^. maximumMemory) ++ ", " ++
                     show (stats ^. instructionsExecuted) ++ ", " ++
                     show (stats ^. readsExecuted) ++ ", " ++
                     show (stats ^. writesExecuted)

updateMaxMemory :: ProgramStats -> ProgramStats
updateMaxMemory stats = (maximumMemory %~ max (stats ^. dynamicMemoryAllocation - stats ^. reclaimedMemory)) stats

stats :: ProgramStats
stats = ProgramStats
    { _staticMemoryAllocation = 0
    , _dynamicMemoryAllocation = 0
    , _reclaimedMemory = 0
    , _maximumMemory = 0
    , _instructionsExecuted = 0
    , _readsExecuted = 0
    , _writesExecuted = 0
    }

data InterpreterState = InterpreterState
    { _heap :: IOArray Word64 Word8
    , _nextHeapCell :: Word64 
    , _programCounter :: Word64
    , _returnStack :: [Word64]
    , _stack :: [Word64]
    , _saveStack :: [Word64]
    , _returnVal :: Word64
    , _registerFile :: IOArray Word64 Word64

    , _programStats :: ProgramStats
    }

makeLenses ''InterpreterState

data InterpreterSettings = ISettings
    { _heapSize :: Word64
    , _debug :: Bool
    , _showExecInstruction :: Bool
    , _showBytecode :: Bool
    , _outputCsv :: Bool
    }

makeLenses ''InterpreterSettings

defaultSettings, debugMode :: InterpreterSettings
defaultSettings = ISettings 1048576 False False False False
debugMode = ISettings 1048576 True False True False
strongDebugMode = ISettings 1048576 True True True False

type Interpreter a = ExceptT ReturnStatus (ReaderT InterpreterSettings (StateT InterpreterState IO)) a

interpret :: InterpreterSettings -> Bytecode -> IO ()
interpret settings bytecode = do
    when (settings ^. debug && not (settings ^. outputCsv)) $ do
        putStrLn $ "Heap size: " ++ show (settings ^. heapSize)
        putStrLn $ "Registers: " ++ show (bytecode ^. registerCount)
        putStrLn ""
        when (settings ^. showBytecode) $ do
            print bytecode
        putStrLn "Running..."
    heapArray <- newArray (0, settings ^. heapSize - 1) 0
    regFileArray <- newArray (0, bytecode ^. registerCount - 1) 0
    let initialState = InterpreterState 
            { _heap = heapArray 
            , _nextHeapCell = 0
            , _programCounter = 0
            , _returnStack = []
            , _stack = []
            , _saveStack = []
            , _returnVal = 0
            , _registerFile = regFileArray
            , _programStats = stats
            }
    (programResult, endState) <- runStateT (runReaderT (runExceptT (forever (fetch >>= step))) settings) initialState
    case programResult of
      Left Success -> do
          when (settings ^. debug && not (settings ^. outputCsv)) $ do
              putStrLn ""
              print (endState ^. programStats)
          when (settings ^. outputCsv) $ putStrLn (showStatsCsv (endState ^. programStats))
          --     putStrLn ""
          --     putStrLn "Result:"
          -- print (endState ^. returnVal)
      Left code -> putStrLn $ "Exception thrown: " ++ show code
      Right _ -> putStrLn "The impossible happened: the program exited without a status."

    where
        fetch :: Interpreter (BytecodeInstruction Word64)
        fetch = do
            pc <- gets (^. programCounter)
            let (label, instruction) = (bytecode ^. instructions) ! pc
            when (settings ^. showExecInstruction) $ do
                case label of
                  Nothing -> pure ()
                  Just l -> liftIO $ print l
                liftIO $ putStrLn $ show pc ++ " " ++ show instruction
            modify (programCounter %~ (+1))
            modify (programStats . instructionsExecuted %~ (+1))
            pure instruction

step :: BytecodeInstruction Word64 -> Interpreter ()
step (Binop op res e1 e2) = do
    v1 <- loadVal e1
    v2 <- loadVal e2
    stepBin op res v1 v2
step (Move res e) = do
    val <- loadVal e
    storeVal res val
step (Write v addr size) = do
    val <- loadVal v
    outAddr <- fromIntegral <$> loadVal addr
    heapArray <- gets (^. heap)
    forM_ (zip [outAddr..outAddr + size - 1] (wordToBytes val)) (liftIO . uncurry (writeArray heapArray))
    modify (programStats . writesExecuted %~ (+1))
step (Read res loc size) = do
    inAddr <- fromIntegral <$> loadVal loc
    heapArray <- gets (^. heap)
    bytes <- forM [inAddr..inAddr + size - 1] (liftIO . readArray heapArray)
    storeVal res (bytesToWord bytes)
    modify (programStats . readsExecuted %~ (+1))
step (MAlloc res size) = do
    allocSize <- fromIntegral <$> loadVal size
    pointer <- gets (^. nextHeapCell)
    totalHeapSpace <- asks (^. heapSize)
    when (totalHeapSpace < pointer + allocSize) $ throwError HeapAllocationFailure

    modify (nextHeapCell %~ (+allocSize))
    modify (programStats . dynamicMemoryAllocation %~ (+allocSize))
    modify (programStats %~ updateMaxMemory)
    storeVal res (fromIntegral pointer)
step (Free ptr size) = do
    base <- loadVal ptr
    heapArray <- gets (^. heap)
    forM_ [base..base + size - 1] $ \addr -> liftIO $ writeArray heapArray addr 255
    modify (programStats . reclaimedMemory %~ (+size))
step (Branch val label) = do
    cond <- loadVal val
    if cond == 0
       then pure ()
       else step (Jump label)
step (Jump label) = do
    modify (programCounter .~ label)
step (Call target) = do
    targetVal <- loadVal target
    pc <- gets (^. programCounter)
    modify ( (returnStack %~ (pc:))
           . (programCounter .~ targetVal)
           )
step Return = do
    cstack <- gets (^. returnStack)
    case cstack of
      (rAddr:rest) -> modify ( (programCounter .~ rAddr)
                             . (returnStack .~ rest)
                             )
      [] -> throwError Success
step (Push val) = do
    pushVal <- loadVal val
    modify (stack %~ (pushVal:))
step (Pop reg) = do
    vstack <- gets (^. stack)
    case vstack of
      (top:rest) -> do
          modify (stack .~ rest)
          case reg of
            Just r -> storeVal r top
            Nothing -> pure ()
      [] -> throwError EmptyArgStack
step (Save val) = do
    pushVal <- loadVal val
    modify (saveStack %~ (pushVal:))
step (Restore reg) = do
    sstack <- gets (^. saveStack)
    case sstack of
      (top:rest) -> do
          modify (saveStack .~ rest)
          storeVal reg top
      [] -> throwError EmptySaveStack
step (PrintF fmt args) = do
    settings <- ask
    argVals <- mapM loadVal args
    let printStr = mkString (printf fmt) argVals
    unless (settings ^. outputCsv) $ liftIO $ putStr printStr
    where
        mkString :: (PrintfArg a, PrintfType r) => (forall r'. PrintfType r' => r') -> [a] -> r
        mkString base [] = base
        mkString base (x:xs) = mkString (base x) xs
step (Throw err) = throwError err
step (StaticAlloc base size) = do
    heapPtr <- gets (^. nextHeapCell)
    totalHeapSpace <- asks (^. heapSize)
    when (base < heapPtr || totalHeapSpace < base + size) $ throwError StaticAllocationFailure

    modify (nextHeapCell .~ base + size)
    modify (programStats . staticMemoryAllocation %~ (+size))
step (CodeLabel _) = pure ()

stepBin :: BinaryOperator -> Register -> Word64 -> Word64 -> Interpreter ()
stepBin Add res v1 v2 = do
    storeVal res (v1 + v2)
stepBin Sub res v1 v2 = do
    storeVal res (v1 - v2)
stepBin Mul res v1 v2 = do
    storeVal res (v1 * v2)
stepBin Div res v1 v2 = do
    storeVal res (v1 `div` v2)
stepBin And res v1 v2 = do
    storeVal res (v1 .&. v2)
stepBin Or res v1 v2 = do
    storeVal res (v1 .|. v2)
stepBin Shift res v1 v2 = do
    storeVal res (shift v1 (fromIntegral v2))
stepBin Equal res v1 v2 = do
    if v1 == v2
       then storeVal res 1
       else storeVal res 0
stepBin NotEqual res v1 v2 = do
    if v1 /= v2
       then storeVal res 1
       else storeVal res 0
stepBin LessThan res v1 v2 = do
    if v1 < v2
       then storeVal res 0
       else storeVal res 1
stepBin GreaterThan res v1 v2 = do
    if v1 > v2
       then storeVal res 0
       else storeVal res 1
stepBin LessThanEqual res v1 v2 = do
    if v1 <= v2
       then storeVal res 0
       else storeVal res 1
stepBin GreaterThanEqual res v1 v2 = do
    if v1 >= v2
       then storeVal res 0
       else storeVal res 1

loadVal :: BytecodeValue Word64 -> Interpreter Word64
loadVal (Immediate imm) = readImm imm
    where
        readImm :: Immediate -> Interpreter Word64
        readImm (Int64 i) = pure (fromIntegral i)
        readImm (Real64 r) = undefined
        readImm (Int1 True) = pure 1
        readImm (Int1 False) = pure 0
        readImm Unit = undefined
        readImm _ = undefined
loadVal (Register (Reg reg)) = do
    rf <- gets (^. registerFile)
    liftIO $ readArray rf reg
loadVal (Register ReturnReg) = gets (^. returnVal)
loadVal (CodeLocation loc) = pure loc

storeVal :: Register -> Word64 -> Interpreter ()
storeVal (Reg reg) v = do
    rf <- gets (^. registerFile)
    liftIO $ writeArray rf reg v
storeVal ReturnReg v = modify (returnVal .~ v)

wordToBytes :: Word64 -> [Word8]
wordToBytes wd = [fromIntegral (shift wd ((-8) * i) .&. 255) | i <- [0..7]]

bytesToWord :: [Word8] -> Word64
bytesToWord wds = sum (zipWith (\i wd -> shift (fromIntegral wd) (8 * i)) [0..] wds)

testInterpreter :: String -> IO ()
testInterpreter input = do
    let bc = testEverything3 input
    putStrLn "Running..."
    interpret debugMode bc

