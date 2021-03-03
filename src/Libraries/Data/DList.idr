module Libraries.Data.DList

%default total

-- Do not re-export the type so that it does not get unfolded in goals
-- and error messages!
export
DList : Type -> Type
DList a = List a -> List a

export
Nil : DList a
Nil = id

export
(::) : a -> DList a -> DList a
(::) a as = (a ::) . as

export
snoc : DList a -> a -> DList a
snoc as a = as . (a ::)

export
appendR : DList a -> List a -> DList a
appendR as bs = as . (bs ++)

export
appendL : List a -> DList a -> DList a
appendL as bs = (as ++) . bs

export
(++) : DList a -> DList a -> DList a
(++) = (.)

export
reify : DList a -> List a
reify as = as []

-- NB: No Functor instance because it's too expensive to reify, map, put back
-- Consider using a different data structure if you need mapping (e.g. a rope)
