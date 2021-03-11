data IsS : (Nat -> Nat) -> Type where
  Indeed : (s : Nat -> Nat) -> s === S -> IsS s

------------------------------------------------------------------------
-- 1.
-- the S pattern is forced by the fact the parameter is instantiated
-- so everything is fine

-- either left implicit
indeed : IsS S -> S === S
indeed (Indeed _ eq) = eq

-- or made explicit
indeed2 : IsS S -> S === S
indeed2 (Indeed S eq) = eq

------------------------------------------------------------------------
-- 2. The S pattern is not forced by the parameter (a generic variable)

-- either don't match on it
indeed3 : IsS s -> s === S
indeed3 (Indeed s eq) = eq

-- or match on the proof that forces it
indeed4 : IsS s -> s === S
indeed4 (Indeed S Refl) = Refl
--              ^ forced by Refl

-- If you don't: too bad!
fail : IsS s -> s === S
fail (Indeed S eq) = eq
--             ^ not Refl, S not forced! OUCH
