{-# LANGUAGE TemplateHaskell #-}
module Interpreter.Interpreter where

import IR.Instructions (BinaryOperator(..), Immediate(..))

import Compiler.Bytecode

import Control.Monad.State
import Control.Monad.Except
import Control.Lens

import Data.Array
import Data.Array.IO
import Data.Word
import Data.Bits

import Debug.Trace

data InterpreterState = InterpreterState
    { _heap :: IOArray Word64 Word8
    , _allocated :: Word64 
    , _programCounter :: Word64
    , _callStack :: [Word64]
    , _stack :: [Word64]
    , _returnVal :: Word64
    , _registerFile :: IOArray Word64 Word64
    , _instructionsExecuted :: Word64
    }

makeLenses ''InterpreterState

data InterpreterSettings = ISettings
    { _heapSize :: Word64
    , _debug :: Bool
    , _showBytecode :: Bool
    }

makeLenses ''InterpreterSettings

defaultSettings, debugMode :: InterpreterSettings
defaultSettings = ISettings 65536 False False
debugMode = ISettings 65536 True True

type Interpreter a = ExceptT Int (StateT InterpreterState IO) a

interpret :: InterpreterSettings -> Bytecode -> IO ()
interpret settings bytecode = do
    when (settings ^. debug) $ do
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
            , _allocated = 0
            , _programCounter = 0
            , _callStack = []
            , _stack = []
            , _returnVal = 0
            , _registerFile = regFileArray
            , _instructionsExecuted = 0
            }
    (programResult, endState) <- runStateT (runExceptT (forever (fetch >>= step))) initialState
    case programResult of
      Left 0 -> do
          when (settings ^. debug) $ do
              putStrLn $ "Total memory use: " ++ show (endState ^. allocated)
              putStrLn $ "Instructions executed: " ++ show (endState ^. instructionsExecuted)
              putStrLn ""
              putStrLn "Result:"
          print (endState ^. returnVal)
      Left (-1) -> putStrLn "Ran out of heap memory!"
      Left code -> putStrLn $ "Exception thrown (" ++ show code ++ ")."

    where
        fetch :: Interpreter (BytecodeInstruction Word64)
        fetch = do
            pc <- gets (^. programCounter)
            let instruction = (bytecode ^. instructions) ! pc
            modify (programCounter %~ (+1))
            modify (instructionsExecuted %~ (+1))
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
step (Read res loc size) = do
    inAddr <- fromIntegral <$> loadVal loc
    heapArray <- gets (^. heap)
    bytes <- forM [inAddr..inAddr + size - 1] (liftIO . readArray heapArray)
    storeVal res (bytesToWord bytes)
step (MAlloc res size) = do
    allocSize <- fromIntegral <$> loadVal size
    pointer <- gets (^. allocated)
    modify (allocated %~ (+allocSize))
    storeVal res (fromIntegral pointer)
step (Free ptr) = do
    pure ()
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
    modify ( (callStack %~ (pc:))
           . (programCounter .~ targetVal)
           )
step Return = do
    cstack <- gets (^. callStack)
    case cstack of
      (rAddr:rest) -> modify ( (programCounter .~ rAddr)
                             . (callStack .~ rest)
                             )
      [] -> throwError 0
step (Push val) = do
    pushVal <- loadVal val
    modify (stack %~ (pushVal:))
step (Pop reg) = do
    vstack <- gets (^. stack)
    case vstack of
      (top:rest) -> do
          modify (stack .~ rest)
          storeVal reg top
      [] -> throwError 3
step (Throw err) = throwError err
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

