||| This file contains several useful interfaces and implementations on BitsX
||| regarding from/to hexadecimal representations. These interfaces are used
||| only by UUID.
module Data.UUID.Hexa

import Data.Bits
import Data.Fin

%default total

-- A single hexadecimal letter corresponds to a Bits4, which is not a
-- builtin type. For convenience in this file, we are treating Bits4
-- as the missing Bits4.
Bits4 : Type
Bits4 = Fin 16

||| Allows to split a BitsX in two halves with respectively
||| most-significant bits and least-significant bits,
||| or to join two sub-parts into a bigger sequence of Bits.
public export
interface Bits b => HalvableBits b where
  0 Half    : Type
  half      : b
  splitBits : b -> (Half, Half)
  joinBits  : Half -> Half -> b

export
HalvableBits Bits8 where
  Half = Bits4
  half = 15
  splitBits n = (toFin $ shiftR n 4, toFin $ n .&. half)
    where
      toFin : Bits8 -> Bits4
      toFin 0 = 0
      toFin 1 = 1
      toFin 2 = 2
      toFin 3 = 3
      toFin 4 = 4
      toFin 5 = 5
      toFin 6 = 6
      toFin 7 = 7
      toFin 8 = 8
      toFin 9 = 9
      toFin 10 = 10
      toFin 11 = 11
      toFin 12 = 12
      toFin 13 = 13
      toFin 14 = 14
      toFin 15 = 15
      toFin _  = 0
  joinBits high low = shiftL (toBits8 high) 4 + toBits8 low
    where
      toBits8 : Bits4 -> Bits8
      toBits8 0 = 0
      toBits8 1 = 1
      toBits8 2 = 2
      toBits8 3 = 3
      toBits8 4 = 4
      toBits8 5 = 5
      toBits8 6 = 6
      toBits8 7 = 7
      toBits8 8 = 8
      toBits8 9 = 9
      toBits8 10 = 10
      toBits8 11 = 11
      toBits8 12 = 12
      toBits8 13 = 13
      toBits8 14 = 14
      toBits8 15 = 15

export
HalvableBits Bits16 where
  Half = Bits8
  half = shiftR oneBits 8
  splitBits n = (cast $ shiftR n 8, cast $ n .&. half)
  joinBits high low = shiftL (cast high) 8 + cast low

export
HalvableBits Bits32 where
  Half = Bits16
  half = shiftR oneBits 16
  splitBits n = (cast $ shiftR n 16, cast $ n .&. half)
  joinBits high low = shiftL (cast high) 16 + cast low

export
HalvableBits Bits64 where
  Half = Bits32
  half = shiftR oneBits 32
  splitBits n = (cast $ shiftR n 32, cast $ n .&. half)
  joinBits high low = shiftL (cast high) 32 + cast low

||| Allows to represents a BitsX value as an hexadecimal String
export
interface ToHexa a where
  toHexaChars : a -> List Char
  toHexa : a -> String
  toHexa n = pack $ toHexaChars n

export %inline
ToHexa (Bits4) where
  toHexaChars 0  = ['0']
  toHexaChars 1  = ['1']
  toHexaChars 2  = ['2']
  toHexaChars 3  = ['3']
  toHexaChars 4  = ['4']
  toHexaChars 5  = ['5']
  toHexaChars 6  = ['6']
  toHexaChars 7  = ['7']
  toHexaChars 8  = ['8']
  toHexaChars 9  = ['9']
  toHexaChars 10 = ['a']
  toHexaChars 11 = ['b']
  toHexaChars 12 = ['c']
  toHexaChars 13 = ['d']
  toHexaChars 14 = ['e']
  toHexaChars 15 = ['f']

export %inline
ToHexa Bits8 where
  toHexaChars n = let (h,l) = splitBits n in toHexaChars h ++ toHexaChars l

export %inline
ToHexa Bits16 where
  toHexaChars n = let (h,l) = splitBits n in toHexaChars h ++ toHexaChars l

export %inline
ToHexa Bits32 where
  toHexaChars n = let (h,l) = splitBits n in toHexaChars h ++ toHexaChars l

export %inline
ToHexa Bits64 where
  toHexaChars n = let (h,l) = splitBits n in toHexaChars h ++ toHexaChars l

||| Allows to represents a BitsX value as an hexadecimal String
public export
interface FromHexa a where
  fromHexaChars : List Char -> Maybe a
  fromHexa : String -> Maybe a
  fromHexa = fromHexaChars . unpack

export %inline
[fin16Hexa] FromHexa (Bits4) where
  fromHexaChars ['0'] = Just 0
  fromHexaChars ['1'] = Just 1
  fromHexaChars ['2'] = Just 2
  fromHexaChars ['3'] = Just 3
  fromHexaChars ['4'] = Just 4
  fromHexaChars ['5'] = Just 5
  fromHexaChars ['6'] = Just 6
  fromHexaChars ['7'] = Just 7
  fromHexaChars ['8'] = Just 8
  fromHexaChars ['9'] = Just 9
  fromHexaChars ['a'] = Just 10
  fromHexaChars ['b'] = Just 11
  fromHexaChars ['c'] = Just 12
  fromHexaChars ['d'] = Just 13
  fromHexaChars ['e'] = Just 14
  fromHexaChars ['f'] = Just 15
  fromHexaChars ['A'] = Just 10
  fromHexaChars ['B'] = Just 11
  fromHexaChars ['C'] = Just 12
  fromHexaChars ['D'] = Just 13
  fromHexaChars ['E'] = Just 14
  fromHexaChars ['F'] = Just 15
  fromHexaChars  _  = Nothing

export %inline
[bits8Hexa] FromHexa Bits8 where
  fromHexaChars [h,l] with (fromHexaChars @{fin16Hexa} [h], fromHexaChars @{fin16Hexa} [l])
    fromHexaChars [h,l] | (Just ch, Just cl) = Just $ joinBits ch cl
    fromHexaChars [h,l] | _ = Nothing
  fromHexaChars _ = Nothing

export %inline
[bits16Hexa] FromHexa Bits16 where
  fromHexaChars [a,b,c,d] with (fromHexaChars @{bits8Hexa} [a,b], fromHexaChars @{bits8Hexa} [c,d])
    fromHexaChars [a,b,c,d] | (Just ch, Just cl) = Just $ joinBits ch cl
    fromHexaChars [a,b,c,d] | _ = Nothing
  fromHexaChars _ = Nothing

export %inline
[bits32Hexa] FromHexa Bits32 where
  fromHexaChars [a,b,c,d,e,f,g,h] with (fromHexaChars @{bits16Hexa} [a,b,c,d], fromHexaChars @{bits16Hexa} [e,f,g,h])
    fromHexaChars [a,b,c,d,e,f,g,h] | (Just ch, Just cl) = Just $ joinBits ch cl
    fromHexaChars [a,b,c,d,e,f,g,h] | _ = Nothing
  fromHexaChars _ = Nothing

export %inline
[bits64Hexa] FromHexa Bits64 where
  fromHexaChars [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p] with (fromHexaChars @{bits32Hexa} [a,b,c,d,e,f,g,h], fromHexaChars @{bits32Hexa} [i,j,k,l,m,n,o,p])
    fromHexaChars [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p] | (Just ch, Just cl) = Just $ joinBits ch cl
    fromHexaChars [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p] | _ = Nothing
  fromHexaChars _ = Nothing


