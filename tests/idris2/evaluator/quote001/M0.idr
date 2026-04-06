module M0

public export
interface I t where
  foo : (x1 : t) -> Unit

public export
[FromLabelFoo] I a where
    foo _ = MkUnit

public export
I Unit where
    foo = foo @{FromLabelFoo}

export
Unit' : Type
Unit' = Unit

UNIT : I Unit
UNIT = %search

export
I Unit' where
  foo = foo @{UNIT}
