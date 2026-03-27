U : Unit

W = MkUnit

data View : Unit -> Type where
  X : View W
  Y : View U

foo : (v : Unit) -> View v -> Unit
foo a@_ X = MkUnit
foo U Y = MkUnit

foo2 : (v : Unit) -> View v -> Unit
foo2 _ X = MkUnit
foo2 U Y = MkUnit
