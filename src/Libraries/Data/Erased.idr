module Libraries.Data.Erased

%default total

public export
record Erased (a : Type) where
  constructor MkErased
  0 runErased : a

export
Functor Erased where
  map f (MkErased x) = MkErased (f x)

export
Applicative Erased where
  pure x = MkErased x
  MkErased f <*> MkErased x = MkErased (f x)

join : Erased (Erased a) -> Erased a
join (MkErased mx) = MkErased (let MkErased x = mx in x)

export
Monad Erased where
  mx >>= f = join (f <$> mx)
