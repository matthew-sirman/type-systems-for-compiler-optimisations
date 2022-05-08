{-# LANGUAGE FunctionalDependencies #-}
module IR.InstructionBuilder where

import IR.Instructions
import IR.DataType

import qualified Data.HashMap.Strict as M
import Data.Maybe (fromJust)

import Control.Monad.State

import Debug.Trace

-- TODO: Consider trying to remove calls to "error"

class Monad m => MonadIRBuilder r e m | m -> r, m -> e where
    addInstruction :: Instruction r e -> m ()
    throwUndefined :: m ()

class PrintFType a

binop :: MonadIRBuilder r e m => BinaryOperator -> m r -> Value r -> Value r -> m (Value r)
binop op getReg lhs rhs = do
    reg <- getReg
    addInstruction $ Binop op reg lhs rhs
    pure (ValVariable (resType op) reg)
    where
        resType :: BinaryOperator -> DataType
        resType Add = I64
        resType Sub = I64
        resType Mul = I64
        resType Div = I64
        resType And = I64
        resType Or = I64
        resType Shift = I64
        resType Equal = I1
        resType NotEqual = I1
        resType LessThan = I1
        resType GreaterThan = I1
        resType LessThanEqual = I1
        resType GreaterThanEqual = I1

write :: MonadIRBuilder r e m => Value r -> Value r -> m ()
write val addr =
    case datatype addr of
      Pointer addrTy ->
        let valTy = datatype val
            Pointer addrTy = datatype addr
         in if compatible valTy addrTy
               then addInstruction $ Write val addr valTy
               else addInstruction $ Write (ValImmediate Undef) (ValImmediate Undef) Void -- error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy
               -- else error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy
      _ -> addInstruction $ Write (ValImmediate Undef) (ValImmediate Undef) Void -- error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy

read :: MonadIRBuilder r e m => m r -> Value r -> m (Value r)
read getReg addr = do
    reg <- getReg
    case datatype addr of
      Pointer dt -> do
          addInstruction $ Read reg addr dt
          pure (ValVariable dt reg)
      ty -> do
          addInstruction $ Read reg (ValImmediate Undef) Void
          pure (ValImmediate Undef)

getElementPtr :: MonadIRBuilder r e m => m r -> Value r -> [Int] -> m (Value r)
getElementPtr getReg src path = do
    reg <- getReg
    case datatype src of
      Pointer struct -> do
          addInstruction $ GetElementPtr reg src path
          pure (ValVariable (Pointer (findType struct path)) reg)
      ty -> do -- error $ "COMPILER ERROR: getelementptr on non-pointer type. " ++ show ty
          addInstruction $ GetElementPtr reg (ValImmediate Undef) path
          pure (ValImmediate Undef)
    where
        findType :: DataType -> [Int] -> DataType
        findType dt [] = dt
        findType (Structure dts) (p:ps) = findType (safeIndex dts (Structure []) p) ps
        findType (NamedStruct (Struct _ names dts _) args) (p:ps) =
            findType (specialise (zip names args) (safeIndex dts (Structure []) p)) ps
        findType (NamedStruct (Alias _ names t) args) ps = findType (specialise (zip names args) t) ps
        findType t path = error $ show (datatype src) ++ ", " ++ show t ++ ", " ++ show path 

        safeIndex :: [a] -> a -> Int -> a
        safeIndex [] e _ = e
        safeIndex (x:_) e 0 = x
        safeIndex (_:xs) e n = safeIndex xs e (n - 1)

bitcast :: MonadIRBuilder r e m => m r -> Value r -> DataType -> m (Value r)
bitcast getReg val dt = do
    reg <- getReg
    addInstruction $ BitCast reg val dt
    pure (ValVariable dt reg)

malloc :: MonadIRBuilder r e m => m r -> DataType -> m (Value r)
malloc getReg dt = do
    reg <- getReg
    addInstruction $ MAlloc reg (ValSizeOf dt)
    pure (ValVariable (Pointer dt) reg)

free :: MonadIRBuilder r e m => Value r -> m ()
free val = addInstruction $ Free val

call :: Show r => MonadIRBuilder r e m => m r -> Value r -> [Value r] -> m (Value r)
call getReg = ((fromJust <$>) .) . makeCall (Just getReg)

voidCall :: Show r => MonadIRBuilder r e m => Value r -> [Value r] -> m ()
voidCall = (void .) . makeCall Nothing

makeCall :: Show r => MonadIRBuilder r e m => Maybe (m r) -> Value r -> [Value r] -> m (Maybe (Value r))
makeCall getReg fun args = do
    res <- sequence getReg
    let FunctionT retType argTypes = datatype fun
    let (matches, subMap) = runState (matchArgs argTypes args) M.empty
    if matches
       then do
           addInstruction $ Call res fun args
           pure (ValVariable (specialise (M.toList subMap) retType) <$> res)
       else error $ "COMPILER ERROR: Invalid arguments in function call. " ++ show args ++ show argTypes
       -- else pure (Just (ValImmediate Undef))
    where
        matchArgs :: [DataType] -> [Value r] -> State (M.HashMap TemplateArgName DataType) Bool
        matchArgs [] _ = pure True
        matchArgs _ [] = pure True
        matchArgs (dt:dts) (v:vs) = matchArg dt (datatype v) .&&. matchArgs dts vs
            where
                matchArg :: DataType -> DataType -> State (M.HashMap TemplateArgName DataType) Bool
                matchArg (FirstOrder fo) (FirstOrder fo') = pure (fo == fo')
                matchArg (NamedStruct s args) (NamedStruct s' args') =
                    foldl (.&&.) (pure (s == s')) (zipWith matchArg args args')
                matchArg (Structure fields) (Structure fields') =
                    foldl (.&&.) (pure True) (zipWith matchArg fields fields')
                matchArg (FunctionT ret args) (FunctionT ret' args') =
                    foldl (.&&.) (matchArg ret ret') (zipWith matchArg args args')
                matchArg (Pointer t) (Pointer t') = do
                    matchArg t t'
                    pure True
                matchArg (TemplateArg targ) t = do
                    exists <- gets (M.lookup targ)
                    case exists of
                      Just t'
                        | t /= t' -> pure False
                      _ -> do
                          modify (M.insert targ t)
                          pure True
                matchArg _ _ = pure False

                (.&&.) :: Monad m => m Bool -> m Bool -> m Bool
                (.&&.) ma mb = do
                    a <- ma
                    if a
                       then mb
                       else pure a

branch :: MonadIRBuilder r e m => Value r -> Label -> m ()
branch cond target = addInstruction $ Branch cond target

jump :: MonadIRBuilder r e m => Label -> m ()
jump label = addInstruction $ Jump label

phi :: MonadIRBuilder r e m => m r -> [PhiNode r] -> m (Value r)
phi getReg [PhiNode (val, _)] = pure val
phi getReg phiNodes = do
    reg <- getReg
    addInstruction $ Phi reg phiNodes
    pure (ValVariable resType reg)
    where
        resType :: DataType
        (Just resType) = foldl findType Nothing phiNodes

        findType :: Maybe DataType -> PhiNode r -> Maybe DataType
        findType Nothing (PhiNode (val, _)) = Just (datatype val)
        findType (Just dt) (PhiNode (val, _))
            | dt == Void = Just valTy
            | valTy == Void = Just dt
            | dt == datatype val = Just dt
            | compatible dt (datatype val) = Just dt
            | otherwise = error ("COMPILER ERROR: Phi branches have different types. " ++ show dt ++ ", "  ++ show (datatype val))
            where
                valTy :: DataType
                valTy = datatype val

ret :: MonadIRBuilder r e m => Maybe (Value r) -> m ()
ret val = addInstruction $ Return val

push :: MonadIRBuilder r e m => Value r -> m ()
push val = addInstruction $ Push val

pop :: MonadIRBuilder r e m => m r -> DataType -> m (Value r)
pop getReg dt = do
    reg <- getReg
    addInstruction $ Pop dt reg
    pure (ValVariable dt reg)

printf :: MonadIRBuilder r e m => String -> [Value r] -> m ()
printf fmt args = addInstruction $ PrintF fmt args

throw :: MonadIRBuilder r e m => e -> m ()
throw err = addInstruction $ Throw err

comment :: MonadIRBuilder r e m => String -> m ()
comment c = addInstruction $ Comment c

