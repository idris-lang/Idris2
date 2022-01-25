-- This ought to go into base at some future point
module Libraries.Data.Span

public export
record Span (a : Type) where
  constructor MkSpan
  start    : Nat
  length   : Nat
  property : a

export
Functor Span where
  map f = { property $= f }

export
Foldable Span where
  foldr c n span = c span.property n

export
Traversable Span where
  traverse f (MkSpan start width prop)
    = MkSpan start width <$> f prop

export
Show a => Show (Span a) where
  show (MkSpan start width prop)
    = concat {t = List} [ "[", show start, "-", show width, "]"
                        , show prop
                        ]
