import Data.Buffer

%default total

public export
interface Singleton (n : Nat) where
  sing : (m : Nat ** m === n)
  sing = (n ** Refl)

Singleton 3 where
Singleton 5 where

export
data ForeignPtr : Type -> Type where
  MkFP : Buffer -> ForeignPtr a

public export
interface Storable (0 a : Type) (n : Nat) | a where
  constructor MkStorable
  peekByteOff : HasIO io => ForeignPtr a -> Int -> io a

  peekElemOff : HasIO io => ForeignPtr a -> Int -> io a
  peekElemOff fp off = peekByteOff fp (off * cast n)

Storable Bits8 8 where
  peekByteOff (MkFP b) off = getBits8 b off
