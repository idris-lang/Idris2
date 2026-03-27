U : Unit

W = MkUnit

data View : Unit -> Type where
  X : View W
  Y : View U

foo : (v : Unit) -> View v -> Unit
foo a X = MkUnit
foo U Y = MkUnit
