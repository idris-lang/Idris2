module Data.UUID

import Data.UUID.Hexa

import Decidable.Equality
import Data.List as L
import Data.Bits
import Data.Fin
import System.Random

%default total

||| Repesentation of an UUID closer to the semantics of the bits
||| as per RFC4122.
public export
record UUID_RFC4122 where
  constructor MkRFC4122
  timelow  : Bits32
  timemid  : Bits16
  timehigh : Bits16
  clockseq : Bits16
  nodelow  : Bits16
  nodehigh : Bits32

export
Show UUID_RFC4122 where
  show (MkRFC4122 tl tm th cs nl nh) =
    "\{toHexa tl}-\{toHexa tm}-\{toHexa th}-\{toHexa cs}-\{toHexa nl}\{toHexa nh}"

||| Economic representation of an UUID with only 2 Bits64.
public export
record UUID where
  constructor MkUUID
  timeBits      : Bits64
  clockNodeBits : Bits64

export
asRFC4122 : UUID -> UUID_RFC4122
asRFC4122 (MkUUID high low) =
  let
    (tl, tmth) = splitBits high
    (tm, th) = splitBits tmth
    (csnl, nh) = splitBits low
    (cs, nl) = splitBits csnl
  in MkRFC4122 tl tm th cs nl nh

export
Show UUID where
  show = show . asRFC4122

export
Interpolation UUID where
  interpolate uuid = show uuid

Eq UUID where
  (==) (MkUUID ta na) (MkUUID tb nb) = ta == tb && na == nb

Ord UUID where
  (<) (MkUUID ta na) (MkUUID tb nb) = (ta < tb) || (ta == tb) && (na < nb)

DecEq UUID where
  decEq (MkUUID ta na) (MkUUID tb nb) with (decEq ta tb, decEq na nb)
    decEq (MkUUID ta na) (MkUUID ta na) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (MkUUID ta na) (MkUUID ta nb) | (Yes Refl, No cb)    = No (\prf => cb $ cong clockNodeBits prf)
    decEq (MkUUID ta na) (MkUUID tb nb) | (No ca,    _)        = No (\prf => ca $ cong timeBits prf)


||| Generates a String with (lowercase) hexadecimal digits,
||| with hyphens respecting the common pattern:
||| `________-____-____-____-____________`
export
toHexa : UUID -> String
toHexa = show

||| This function is very permissive and will accept any sequence of
||| 32 hexadecimal digits (upper or lower), interspersed with any random
||| noise.
export
fromHexa : String -> Maybe UUID
fromHexa s =
  let
    cs = unpack s
    ls = map toLower cs
    hs = filter isHexDigit ls
  in
    if (length hs /= 32)
    then Nothing
    else pure $ MkUUID !(fromHexaChars @{bits64Hexa} $ L.take 16 hs) !(fromHexaChars @{bits64Hexa} $ L.drop 16 hs)


||| This function generates an UUID following the RFC4122 section 4.4,
||| with version 4 as defined in section 4.1.3.
||| @see https://datatracker.ietf.org/doc/html/rfc4122#section-4.4
export
randomUUID : HasIO io => io UUID
randomUUID = pure $ MkUUID !(map setVersionBits randomBits64) !(map setVariantBits randomBits64)
  where
    randomBits32 : io Bits32
    randomBits32 = map cast (the (io Int32) randomIO)

    randomBits64 : io Bits64
    randomBits64 = pure $ joinBits !randomBits32 !randomBits32

    -- UUID has a 4 there:
    -- ________-____-4___-____-____________
    setVersionBits : Bits64 -> Bits64
    setVersionBits n =
      let
        m = clearBit n 12
        l = clearBit m 13
        o = setBit   l 14
        p = clearBit o 15
      in p

    -- UUID has any of {8,9,a,b} at the X:
    -- ________-____-____-X___-____________
    setVariantBits : Bits64 -> Bits64
    setVariantBits n =
      let
        m = clearBit n 62
        l = setBit   m 63
      in l

||| Nil is the special UUID with all bits at 0
||| @see https://datatracker.ietf.org/doc/html/rfc4122#section-4.1.7
export
nil : UUID
nil = MkUUID 0 0
