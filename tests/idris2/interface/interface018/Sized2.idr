import Data.Buffer

export
data ForeignPtr : Type -> Type where
  MkFP : Buffer -> ForeignPtr a

public export
interface Storable a where
  size : Int

  peekByteOff : HasIO io => ForeignPtr a -> Int -> io a

  peekElemOff : HasIO io => ForeignPtr a -> Int -> io a
  peekElemOff fp off = peekByteOff fp (off * size {a})

Storable Bits8 where
  size = 8
  peekByteOff (MkFP b) off = getBits8 b off
