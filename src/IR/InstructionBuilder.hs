{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module IR.InstructionBuilder where

import IR.Instructions
import IR.DataType

import Debug.Trace

-- TODO: Consider trying to remove calls to "error"

class Monad m => MonadIRBuilder r m | m -> r where
    addInstruction :: Instruction r -> m ()

binop :: MonadIRBuilder r m => BinaryOperator -> m r -> Value r -> Value r -> m (Value r)
binop op getReg lhs rhs = do
    reg <- getReg
    addInstruction $ Binop op reg lhs rhs
    pure (ValVariable (resType op) reg)
    where
        resType :: BinaryOperator -> DataType
        resType Add = i64
        resType Sub = i64
        resType Mul = i64
        resType Div = i64
        resType And = i64
        resType Or = i64
        resType Equal = i1
        resType NotEqual = i1
        resType LessThan = i1
        resType GreaterThan = i1
        resType LessThanEqual = i1
        resType GreaterThanEqual = i1

write :: MonadIRBuilder r m => Value r -> Value r -> m ()
write val addr =
    let valTy = dataType val
        Pointer addrTy = dataType addr
     in if valTy == addrTy
           then addInstruction $ Write val addr valTy
           else error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy

read :: MonadIRBuilder r m => m r -> Value r -> m (Value r)
read getReg addr = do
    reg <- getReg
    let Pointer dt = dataType addr
    addInstruction $ Read reg addr dt
    pure (ValVariable dt reg)

getElementPtr :: MonadIRBuilder r m => m r -> Value r -> [Int] -> m (Value r)
getElementPtr getReg src path = do
    reg <- getReg
    let Pointer struct = dataType src
        dt = findType struct path
    addInstruction $ GetElementPtr reg src path
    pure (ValVariable (Pointer dt) reg)
    where
        findType :: DataType -> [Int] -> DataType
        findType dt [] = dt
        findType (Structure dts) (p:ps) = findType (dts !! p) ps
        findType (NamedStruct (Struct _ dts _)) (p:ps) = findType (dts !! p) ps

bitcast :: MonadIRBuilder r m => m r -> Value r -> DataType -> m (Value r)
bitcast getReg val dt = do
    reg <- getReg
    addInstruction $ BitCast reg val dt
    pure (ValVariable dt reg)

malloc :: MonadIRBuilder r m => m r -> DataType -> m (Value r)
malloc getReg dt = do
    reg <- getReg
    addInstruction $ MAlloc reg (ValSizeOf dt)
    pure (ValVariable (Pointer dt) reg)

call :: MonadIRBuilder r m => m r -> Value r -> [Value r] -> m (Value r)
call getReg fun args = do
    res <- getReg
    addInstruction $ Call (Just res) fun args
    let FunctionT retType _ = dataType fun
    pure (ValVariable retType res)

voidCall :: MonadIRBuilder r m => Value r -> [Value r] -> m ()
voidCall fun args = addInstruction $ Call Nothing fun args

branch :: MonadIRBuilder r m => Value r -> Label -> m ()
branch cond target = addInstruction $ Branch cond target

jump :: MonadIRBuilder r m => Label -> m ()
jump label = addInstruction $ Jump label

phi :: MonadIRBuilder r m => m r -> [PhiNode r] -> m (Value r)
phi getReg [PhiNode (val, _)] = pure val
phi getReg phiNodes = do
    reg <- getReg
    addInstruction $ Phi reg phiNodes
    pure (ValVariable resType reg)
    where
        resType :: DataType
        (Just resType) = foldl findType Nothing phiNodes

        findType :: Maybe DataType -> PhiNode r -> Maybe DataType
        findType Nothing (PhiNode (val, _)) = Just (dataType val)
        findType (Just dt) (PhiNode (val, _))
            | dt == FirstOrder Void = Just valTy
            | valTy == FirstOrder Void = Just dt
            | dt == dataType val = Just dt
            | otherwise = error "COMPILER ERROR: Phi branches have different types."
            where
                valTy :: DataType
                valTy = dataType val

ret :: MonadIRBuilder r m => Maybe (Value r) -> m ()
ret val = addInstruction $ Return val

throw :: MonadIRBuilder r m => Int -> m ()
throw err = addInstruction $ Throw err

