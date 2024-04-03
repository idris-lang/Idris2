module Test

private
infixr 5 ~:>

public export
infixr 5 ~>
export
infixl 5 |>

public export
record HasComp (x : Type) where
  constructor MkComp
  (~:>) : x -> x -> Type
  comp : {0 a, b, c : x} -> a ~:> b -> b ~:> c -> a ~:> c

public export
(~>) : (s : HasComp a) => a -> a -> Type
(~>) = (~:>) s

export
typesHaveComp : HasComp Type
typesHaveComp = MkComp (\x, y => x -> y) (flip (.))
