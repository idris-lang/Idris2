%default total

namespace Bits8
  export
  data LessThan : Bits8 -> Bits8 -> Type where
    MkLessThan : (a < b) === True -> LessThan a b

  export
  %hint
  mkLessThan : (a < b) === True -> LessThan a b
  mkLessThan = MkLessThan

data Digit : Bits8 -> Type where
  MkDigit : (x : Bits8) -> {auto prf1 : LessThan 47 x} -> {auto prf2 : LessThan x 58} -> Digit x

prf1 : Digit 51
prf1 = MkDigit 51

dis0 : Digit 51 -> Void
dis0 (MkDigit _ {prf1=Refl}) impossible

