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
    , _returnVal :: Word64
    , _argRegisters :: IOArray Word64 Word64
    , _registerFile :: IOArray Word64 Word64
    }

makeLenses ''InterpreterState

data InterpreterSettings = ISettings
    { _heapSize :: Word64
    , _argRegSize :: Word64
    }

makeLenses ''InterpreterSettings

defaultSettings = ISettings 256 16

type Interpreter a = ExceptT Int (StateT InterpreterState IO) a

interpret :: InterpreterSettings -> Bytecode -> IO ()
interpret settings bytecode = do
    heapArray <- newArray (0, settings ^. heapSize - 1) 0
    regFileArray <- newArray (0, bytecode ^. registerCount - 1) 0
    argFileArray <- newArray (0, settings ^. argRegSize - 1) 0
    let initialState = InterpreterState 
            { _heap = heapArray 
            , _allocated = 0
            , _programCounter = 0
            , _callStack = []
            , _returnVal = 0
            , _argRegisters = argFileArray
            , _registerFile = regFileArray
            }
    (programResult, endState) <- runStateT (runExceptT (forever (fetch >>= step))) initialState
    case programResult of
      Left 0 -> print (endState ^. returnVal)
      Left (-1) -> putStrLn "Ran out of heap memory!"

    where
        fetch :: Interpreter (BytecodeInstruction Word64)
        fetch = do
            pc <- gets (^. programCounter)
            let instruction = (bytecode ^. instructions) ! pc
            modify (programCounter %~ (+1))
            -- rf <- gets (^. registerFile) >>= liftIO . getElems
            -- af <- gets (^. argRegisters) >>= liftIO . getElems
            -- rv <- gets (^. returnVal)
            -- trace (show pc ++ ": " ++ show rf ++ ", " ++ show af ++ ", " ++ show rv) $ pure ()
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
step (Call (Direct target)) = do
    pc <- gets (^. programCounter)
    modify ( (callStack %~ (pc:))
           . (programCounter .~ target)
           )
step (Call (Indirect target)) = do
    t <- loadVal target
    step (Call (Direct t))
step (Branch val label) = do
    cond <- loadVal val
    if cond == 0
       then pure ()
       else step (Jump label)
step (Jump label) = do
    modify (programCounter .~ label)
step Return = do
    stack <- gets (^. callStack)
    case stack of
      (rAddr:rest) -> modify ( (programCounter .~ rAddr)
                             . (callStack .~ rest)
                             )
      [] -> throwError 0
step (Throw err) = throwError err

stepBin :: BinaryOperator -> Register -> Word64 -> Word64 -> Interpreter ()
stepBin Add res v1 v2 = do
    storeVal res (v1 + v2)
stepBin Equal res v1 v2 = do
    if v1 == v2
       then storeVal res 1
       else storeVal res 0

loadVal :: BytecodeValue -> Interpreter Word64
loadVal (Immediate imm) = readImm imm
    where
        readImm :: Immediate -> Interpreter Word64
        readImm (Int64 i) = pure (fromIntegral i)
        readImm (Real64 r) = undefined
        readImm (Bool b) = undefined
        readImm Unit = undefined
loadVal (Register (Reg reg)) = do
    rf <- gets (^. registerFile)
    liftIO $ readArray rf reg
loadVal (Register (ArgReg a)) = do
    rf <- gets (^. argRegisters)
    liftIO $ readArray rf a
loadVal (Register ReturnReg) = gets (^. returnVal)

storeVal :: Register -> Word64 -> Interpreter ()
storeVal (Reg reg) v = do
    rf <- gets (^. registerFile)
    liftIO $ writeArray rf reg v
storeVal (ArgReg a) v = do
    rf <- gets (^. argRegisters)
    liftIO $ writeArray rf a v
storeVal ReturnReg v = modify (returnVal .~ v)

wordToBytes :: Word64 -> [Word8]
wordToBytes wd = [fromIntegral (shift wd ((-8) * i) .&. 255) | i <- [0..7]]

bytesToWord :: [Word8] -> Word64
bytesToWord wds = sum (zipWith (\i wd -> shift (fromIntegral wd) (8 * i)) [0..] wds)

