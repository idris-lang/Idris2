module Libraries.Data.DList

%default total

export
record DList (a : Type) where
  constructor MkDList
  runDList : List a -> List a

export %inline
Nil : DList a
Nil = MkDList id

export %inline
singleton : a -> DList a
singleton a = MkDList (a ::)

export %inline
(::) : a -> DList a -> DList a
(::) a as = MkDList ((a ::) . runDList as)

export %inline
snoc : DList a -> a -> DList a
snoc as a = MkDList (runDList as . (a ::))

export %inline
appendR : DList a -> List a -> DList a
appendR as bs = MkDList (runDList as . (bs ++))

export %inline
appendL : List a -> DList a -> DList a
appendL as bs = MkDList ((as ++) . runDList bs)

export %inline
(++) : DList a -> DList a -> DList a
as ++ bs = MkDList (runDList as . runDList bs)

export %inline
reify : DList a -> List a
reify as = runDList as []

-- NB: No Functor instance because it's too expensive to reify, map, put back
-- Consider using a different data structure if you need mapping (e.g. a rope)

export %inline
Semigroup (DList a) where
  xs <+> ys = xs ++ ys

export %inline
Monoid (DList a) where
  neutral = []

export %inline
FromString (DList String) where
  fromString = singleton
