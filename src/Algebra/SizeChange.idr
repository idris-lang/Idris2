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

-- information order
export
Ord SizeChange where
  compare Unknown Unknown = EQ
  compare Unknown _ = LT
  compare _ Unknown = GT
  compare Same Same = EQ
  compare Same _ = LT
  compare _ Same = GT
  compare Smaller Smaller = EQ

  max Unknown y = y
  max Same Unknown = Same
  max Same y = y
  max Smaller y = Smaller -- holds definitionally!
