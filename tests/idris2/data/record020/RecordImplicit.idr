record WithShow (ty : Type) where
  constructor MkWS
  {auto hasShow : Show ty}
  name : String

foo : WithShow ty -> WithShow ty
foo ws = { name := "meh" } ws
