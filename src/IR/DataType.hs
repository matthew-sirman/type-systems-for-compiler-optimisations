module IR.DataType where

import Data.List (intercalate)

class DataTypeContainer c where
    datatype :: c -> DataType

type StructName = String

data FirstOrder
    = Int1T
    | Int64T
    | Real64T
    | UnitT
    | Void
    deriving Eq

instance Show FirstOrder where
    show Int1T = "i1"
    show Int64T = "i64"
    show Real64T = "r64"
    show UnitT = "unit"
    show Void = "void"

data Struct = Struct StructName [DataType] Bool
    deriving Eq

instance Show Struct where
    show (Struct name ts packed) = name ++ " = type " ++ open ++ " " ++ intercalate ", " (map show ts) ++ " " ++ close
        where
            open, close :: String
            (open, close)
                | packed = ("<{", "}>")
                | otherwise = ("{", "}")

data DataType
    = FirstOrder FirstOrder
    | NamedStruct Struct
    | Structure [DataType]
    | FunctionT DataType [DataType]
    | Pointer DataType
    deriving Eq

instance Show DataType where
    show (FirstOrder t) = show t
    show (NamedStruct (Struct name _ _)) = name
    show (Structure ts) = "{" ++ intercalate ", " (map show ts) ++ "}"
    show (FunctionT ret args) = show ret ++ " (" ++ intercalate ", " (map show args) ++ ")"
    show (Pointer t) = show t ++ "*"

ptrSize :: Num a => a
ptrSize = 8

i1, i64, r64 :: DataType
i1 = FirstOrder Int1T
i64 = FirstOrder Int64T
r64 = FirstOrder Real64T

sizeof :: Integral a => DataType -> a
sizeof (FirstOrder t) = coveringBytes (primBits t)
sizeof (NamedStruct (Struct _ ts False)) = sum (map sizeof ts)
sizeof (NamedStruct (Struct _ ts True)) = calcPacked ts 0
    where
        calcPacked :: Integral a => [DataType] -> a -> a
        calcPacked [] acc = coveringBytes acc
        calcPacked (t@(FirstOrder prim):ts) acc
            | align prim = coveringBytes acc + sizeof t + calcPacked ts 0
            | otherwise = calcPacked ts (acc + primBits prim)
        calcPacked (t:ts) acc = coveringBytes acc + sizeof t + calcPacked ts 0
sizeof (Structure ts) = sum (map sizeof ts)
sizeof (FunctionT _ _) = ptrSize
sizeof (Pointer _) = ptrSize

elementPtrOffset :: Integral a => DataType -> [Int] -> (a, a)
elementPtrOffset dt path = divMod (epo 0 dt path) 8
    where
        epo :: Integral a => a -> DataType -> [Int] -> a
        epo bits (FirstOrder prim) []
            | not (align prim) = bits
        epo bits _ [] = completeByte bits
        epo bits (Structure ts) (p:ps) =
            let (bypass, next:_) = splitAt p ts
             in epo (completeByte bits + 8 * sum (map sizeof bypass)) next ps
        epo bits (NamedStruct (Struct _ ts packed)) (p:ps)
            | packed =
                let (bypass, next:_) = splitAt p ts
                 in epo (completeByte bits + calcPackedOffset bypass 0) next ps
            | otherwise =
                let (bypass, next:_) = splitAt p ts
                 in epo (completeByte bits + 8 * sum (map sizeof bypass)) next ps

        calcPackedOffset :: Integral a => [DataType] -> a -> a
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
primBits Void = 0

coveringBytes :: Integral a => a -> a
coveringBytes bits = (bits + 7) `div` 8

completeByte :: Integral a => a -> a
completeByte bits = 8 * coveringBytes bits

align :: FirstOrder -> Bool
align Int1T = False
align _ = True

