{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module IR.InstructionBuilder where

import IR.Instructions
import IR.DataType

import qualified Data.HashMap.Strict as M

import Control.Monad.State

import Debug.Trace

-- TODO: Consider trying to remove calls to "error"

class Monad m => MonadIRBuilder r m | m -> r where
    addInstruction :: Instruction r -> m ()

class PrintFType a

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
    case datatype addr of
      Pointer addrTy ->
        let valTy = datatype val
            Pointer addrTy = datatype addr
         in if compatible valTy addrTy
               then addInstruction $ Write val addr valTy
               else addInstruction $ Write (ValImmediate Undef) (ValImmediate Undef) (FirstOrder Void) -- error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy
               -- else error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy
      _ -> addInstruction $ Write (ValImmediate Undef) (ValImmediate Undef) (FirstOrder Void) -- error $ "COMPILER ERROR: Write value type and address type incompatible. " ++ show valTy ++ ", " ++ show addrTy

read :: MonadIRBuilder r m => m r -> Value r -> m (Value r)
read getReg addr = do
    reg <- getReg
    case datatype addr of
      Pointer dt -> do
          addInstruction $ Read reg addr dt
          pure (ValVariable dt reg)
      ty -> do
          addInstruction $ Read reg (ValImmediate Undef) (FirstOrder Void)
          pure (ValImmediate Undef)

getElementPtr :: MonadIRBuilder r m => m r -> Value r -> [Int] -> m (Value r)
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
        findType (Structure dts) (p:ps) = findType (dts !! p) ps
        findType (NamedStruct (Struct _ names dts _) args) (p:ps) = findType (specialise (zip names args) (dts !! p)) ps
        findType (NamedStruct (Alias _ names t) args) ps = findType (specialise (zip names args) t) ps
        findType t path = error $ show (datatype src) ++ ", " ++ show t ++ ", " ++ show path 

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

call :: Show r => MonadIRBuilder r m => m r -> Value r -> [Value r] -> m (Value r)
call getReg fun args = do
    res <- getReg
    let FunctionT retType argTypes = datatype fun
    let (matches, subMap) = runState (matchArgs argTypes args) M.empty
    if matches
       then do
           addInstruction $ Call (Just res) fun args
           pure (ValVariable (specialise (M.toList subMap) retType) res)
       else error $ "COMPILER ERROR: Invalid arguments in function call. " ++ show args ++ show argTypes
    where
        matchArgs :: [DataType] -> [Value r] -> State (M.HashMap TemplateArgName DataType) Bool
        matchArgs [] [] = pure True
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
                matchArg (Pointer (FirstOrder Void)) (Pointer _) = pure True
                matchArg (Pointer t) (Pointer t') = matchArg t t'
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
        findType Nothing (PhiNode (val, _)) = Just (datatype val)
        findType (Just dt) (PhiNode (val, _))
            | dt == FirstOrder Void = Just valTy
            | valTy == FirstOrder Void = Just dt
            | dt == datatype val = Just dt
            | otherwise = error "COMPILER ERROR: Phi branches have different types."
            where
                valTy :: DataType
                valTy = datatype val

ret :: MonadIRBuilder r m => Maybe (Value r) -> m ()
ret val = addInstruction $ Return val

printf :: MonadIRBuilder r m => String -> [Value r] -> m ()
printf fmt args = addInstruction $ PrintF fmt args

throw :: MonadIRBuilder r m => Int -> m ()
throw err = addInstruction $ Throw err

