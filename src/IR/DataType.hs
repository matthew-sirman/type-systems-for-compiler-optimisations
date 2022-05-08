{-# LANGUAGE PatternSynonyms #-}
module IR.DataType where

import Data.List (intercalate)
import Data.Semigroup
import qualified Data.HashMap.Strict as M

import Debug.Trace

class DataTypeContainer c where
    datatype :: c -> DataType

type StructName = String
type TemplateArgName = String

data FirstOrder
    = Int1T
    | Int64T
    | Real64T
    | UnitT
    | VoidT
    deriving Eq

instance Show FirstOrder where
    show Int1T = "i1"
    show Int64T = "i64"
    show Real64T = "r64"
    show UnitT = "unit"
    show VoidT = "void"

data Struct
    = Struct StructName [TemplateArgName] [DataType] Bool
    | Union StructName [TemplateArgName] [DataType]
    | Alias StructName [TemplateArgName] DataType
    | ForwardDecl StructName [TemplateArgName]

structBaseName :: Struct -> StructName
structBaseName (Struct name _ _ _) = name
structBaseName (Union name _ _) = name
structBaseName (Alias name _ _) = name
structBaseName (ForwardDecl name _) = name

structArgs :: Struct -> [TemplateArgName]
structArgs (Struct _ args _ _) = args
structArgs (Union _ args _) = args
structArgs (Alias _ args _) = args
structArgs (ForwardDecl _ args) = args

structName :: Struct -> StructName
structName (Struct name [] _ _) = name
structName (Union name [] _) = name
structName (Alias name [] _) = name
structName (ForwardDecl name []) = name
structName (Struct name args _ _) = name ++ "<" ++ intercalate ", " args ++ ">"
structName (Union name args _) = name ++ "<" ++ intercalate ", " args ++ ">"
structName (Alias name args _) = name ++ "<" ++ intercalate ", " args ++ ">"
structName (ForwardDecl name args) = name ++ "<" ++ intercalate ", " args ++ ">"

appliedStructName :: Struct -> [DataType] -> StructName
appliedStructName (Struct name _ _ _) [] = name
appliedStructName (Union name _ _) [] = name
appliedStructName (Alias name _ _) [] = name
appliedStructName (ForwardDecl name _) [] = name
appliedStructName (Struct name _ _ _) args = name ++ "<" ++ intercalate ", " (map show args) ++ ">"
appliedStructName (Union name _ _) args = name ++ "<" ++ intercalate ", " (map show args) ++ ">"
appliedStructName (Alias name _ _) args = name ++ "<" ++ intercalate ", " (map show args) ++ ">"
appliedStructName (ForwardDecl name _) args = name ++ "<" ++ intercalate ", " (map show args) ++ ">"

instance Show Struct where
    show struct@(Struct _ _ ts packed) = structName struct ++ " = type " ++ open ++ " " ++ intercalate ", " (map show ts) ++ " " ++ close ++ "\n"
        where
            open, close :: String
            (open, close)
                | packed = ("<{", "}>")
                | otherwise = ("{", "}")
    show struct@(Union _ _ alts) = structName struct ++ " = union" ++
                                 " { " ++ intercalate ", " (map show alts) ++ " }" ++ "\n"
    show struct@(Alias _ _ t) = structName struct ++ " = alias " ++ show t ++ "\n"
    show struct@(ForwardDecl _ _) = structName struct ++ " = type" ++ "\n"

instance Eq Struct where
    (Struct n args ts packed) == (Struct n' args' ts' packed') = n == n' -- && args == args' && ts == ts' && packed == packed'
    (Union n args ts) == (Union n' args' ts') = n == n' -- && args == args' && tag == tag' && ts == ts'
    (ForwardDecl n _) == (ForwardDecl n' _) = n == n'
    (ForwardDecl n _) == t = n == structBaseName t
    t == (ForwardDecl n _) = n == structBaseName t
    (Alias _ _ t) == (Alias _ _ t') = t == t'
    (Alias _ _ (NamedStruct t _)) == t' = t == t'
    t == (Alias _ _ (NamedStruct t' _)) = t == t'
    _ == _ = False

data DataType
    = FirstOrder FirstOrder
    | NamedStruct Struct [DataType]
    | Structure [DataType]
    | FunctionT DataType [DataType]
    | Pointer DataType
    | TemplateArg TemplateArgName
    deriving Eq

instance Show DataType where
    show (FirstOrder t) = show t
    show (NamedStruct struct args) = appliedStructName struct args
    show (Structure ts) = "{" ++ intercalate ", " (map show ts) ++ "}"
    show (FunctionT ret args) = show ret ++ " (" ++ intercalate ", " (map show args) ++ ")"
    show (Pointer t) = show t ++ "*"
    show (TemplateArg name) = name

specialise :: [(TemplateArgName, DataType)] -> DataType -> DataType
specialise assocs = subst
    where
        subMap :: M.HashMap TemplateArgName DataType
        subMap = M.fromList assocs

        subst :: DataType -> DataType
        subst fo@(FirstOrder _) = fo
        subst (NamedStruct struct args) = NamedStruct struct (map subst args)
        subst (Structure ts) = Structure (map subst ts)
        subst (FunctionT ret args) = FunctionT (subst ret) (map subst args)
        subst (Pointer t) = Pointer (subst t)
        subst t@(TemplateArg name) = M.lookupDefault t name subMap

isFunctionType :: DataType -> Bool
isFunctionType (FunctionT {}) = True
isFunctionType _ = False

ptrSize :: Num a => a
ptrSize = 8

-- i1, i64, r64, void, voidPtr :: DataType
pattern I1 = FirstOrder Int1T
pattern I64 = FirstOrder Int64T
pattern R64 = FirstOrder Real64T
pattern Void = FirstOrder VoidT
pattern VoidPtr = Pointer Void

sizeof :: (Bounded a, Integral a) => DataType -> a
sizeof (FirstOrder t) = coveringBytes (primBits t)
sizeof (NamedStruct struct args) = sizeofStruct struct args
sizeof (Structure ts) = sum (map sizeof ts)
sizeof (FunctionT _ _) = ptrSize
sizeof (Pointer _) = ptrSize
sizeof (TemplateArg name) = error $ "Size of unknown template argument " ++ name

sizeofStruct :: (Bounded a, Integral a) => Struct -> [DataType] -> a
sizeofStruct (Struct _ argNames ts False) args =
    sum (map (sizeof . specialise (zip argNames args)) ts)
sizeofStruct (Struct _ _ ts True) args = calcPacked ts 0
    where
        calcPacked :: (Bounded a, Integral a) => [DataType] -> a -> a
        calcPacked [] acc = coveringBytes acc
        calcPacked (t@(FirstOrder prim):ts) acc
            | align prim = coveringBytes acc + sizeof t + calcPacked ts 0
            | otherwise = calcPacked ts (acc + primBits prim)
        calcPacked (t:ts) acc = coveringBytes acc + sizeof t + calcPacked ts 0
sizeofStruct (Union _ argNames alts) args =
    getMax (foldMap (Max . sizeof . specialise (zip argNames args)) alts)
sizeofStruct (Alias _ argNames t) args = sizeof (specialise (zip argNames args) t)
sizeofStruct _ _ = error "Size of forward declared struct"

elementPtrOffset :: (Bounded a, Integral a) => DataType -> [Int] -> (a, a)
elementPtrOffset dt path = divMod (epo 0 dt path) 8
    where
        epo :: (Bounded a, Integral a) => a -> DataType -> [Int] -> a
        epo bits (FirstOrder prim) []
            | not (align prim) = bits
        epo bits _ [] = completeByte bits
        epo bits (Structure ts) (p:ps) =
            let (bypass, next:_) = splitAt p ts
             in epo (completeByte bits + 8 * sum (map sizeof bypass)) next ps
        epo bits (NamedStruct (Struct _ _ ts packed) _) (p:ps)
            | packed =
                let (bypass, next:_) = splitAt p ts
                 in epo (completeByte bits + calcPackedOffset bypass 0) next ps
            | otherwise =
                let (bypass, next:_) = splitAt p ts
                 in epo (completeByte bits + 8 * sum (map sizeof bypass)) next ps
        epo bits (NamedStruct (Alias _ _ t) _) ps = epo bits t ps
        epo _ _ _ = error "Illegal element offset"

        calcPackedOffset :: (Bounded a, Integral a) => [DataType] -> a -> a
        calcPackedOffset [] acc = acc
        calcPackedOffset (FirstOrder prim:ts) acc
            | align prim = calcPackedOffset ts (primBits prim + completeByte acc)
            | otherwise = calcPackedOffset ts (primBits prim + acc)
        calcPackedOffset (t:ts) acc = calcPackedOffset ts (8 * sizeof t + completeByte acc)

primBits :: Integral a => FirstOrder -> a
primBits Int1T = 1
primBits Int64T = 64
primBits Real64T = 64
primBits UnitT = 0
primBits VoidT = 0

coveringBytes :: Integral a => a -> a
coveringBytes bits = (bits + 7) `div` 8

completeByte :: Integral a => a -> a
completeByte bits = 8 * coveringBytes bits

align :: FirstOrder -> Bool
align Int1T = False
align _ = True

compatible :: DataType -> DataType -> Bool
compatible (FirstOrder fo) (FirstOrder fo') = fo == fo'
compatible (NamedStruct s args) (NamedStruct s' args') =
    s == s' && and (zipWith compatible args args')
compatible (NamedStruct (Alias _ as t) args) t' =
    compatible (specialise (zip as args) t) t'
compatible t (NamedStruct (Alias _ as t') args) =
    compatible t (specialise (zip as args) t')
compatible (Structure ts) (Structure ts') = and (zipWith compatible ts ts')
compatible (Pointer _) (FunctionT {}) = True
compatible (FunctionT {}) (Pointer _) = True
compatible (FunctionT ret args) (FunctionT ret' args') =
    compatible ret ret' && and (zipWith compatible args args')
compatible (Pointer _) (Pointer _) = True
compatible _ _ = False

