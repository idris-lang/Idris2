A : Type
A = ((), Nat)

Z : A
Z = ((), 0)

S : A -> A
S a = ((), S (snd a))

data P : A -> Type where
    C : P (S a)

data Q : A -> Type where
    U : Q Z
    V : Q (S a)

oopsie : P a -> Q a -> Void
oopsie C U impossible

bad : Void
bad = oopsie (C {a = Z}) (V {a = Z})
