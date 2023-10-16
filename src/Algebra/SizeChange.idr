module Algebra.SizeChange

import Algebra.Semiring

import Libraries.Text.PrettyPrint.Prettyprinter

public export
data SizeChange = Smaller | Same | Unknown

export
Semigroup SizeChange where
  -- Same is a neutral
  Unknown <+> _ = Unknown
  Same <+> c = c
  _ <+> Unknown = Unknown
  Smaller <+> _ = Smaller

export
Monoid SizeChange where
  neutral = Same

export
Show SizeChange where
  show Smaller = "Smaller"
  show Same = "Same"
  show Unknown = "Unknown"

export
Eq SizeChange where
  Smaller == Smaller = True
  Same == Same = True
  Unknown == Unknown = True
  _ == _ = False

export
Ord SizeChange where
  compare Smaller Smaller = EQ
  compare Smaller _ = LT
  compare _ Smaller = GT
  compare Same Same = EQ
  compare Same _ = LT
  compare _ Same = GT
  compare Unknown Unknown = EQ
