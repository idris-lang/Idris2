
------------- Example 1 ----------------
natInjective : (x, y : Nat) -> S x === S y -> x === y
natInjective x x Refl = Refl

succNotZero : (x : Nat) -> Not (S x === Z)
succNotZero x Refl impossible

peanoNat : (a  : Type
        ** n0  : a
        ** ns  : a -> a
        ** inj : ((x, y : a) -> ns x === ns y -> x === y)
        **       (x : a) -> Not (ns x === n0))
peanoNat = MkDPair
             Nat
         $ MkDPair
             Z
         $ MkDPair -- {a = Nat -> Nat}
             S
         $ MkDPair
             natInjective
             succNotZero

------------- Example 2 ----------------
ac : forall r. ((x : a) -> (y : b ** r x y)) -> (f : a -> b ** (x : a) -> r x (f x))
ac g = (\x => fst (g x) ** \x => snd (g x))

------------- Example 3 ----------------
idid1 : forall A. (f : A -> A ** (x : A) -> f x = x)
idid1 = MkDPair id (\x => Refl)

