namespace XX
    export
    g : Nat -> Nat
    g = S . S

    export
    H : Nat
    H = Z

-- InTerm
w : Equal H Z
failing "Can't solve constraint"
    w = Refl

f : Nat -> Nat
f = S

u : Equal (f (f Z)) (g Z)
failing "Can't solve constraint"
    u = Refl

data H2 : (a : Nat) -> Type where
    MkH2 : a -> H2 Z

-- InLHS
hh : H2 H -> Nat
failing "Can't solve constraint"
  hh (MkH2 _) = Z

-- InMatch
test : Nat -> Nat
failing "Can't match on H"
    test x = case x of
        H => 0
        _ => 1

data FN : a -> Type where
    MkFN : (0 a : _) -> FN a

namespace XX2
    export
    FN2 : (a: _) -> FN a
    FN2 a = MkFN a

    export
    0 FN3 : (0 a: _) -> FN a
    FN3 a = MkFN a

w2 : Equal (FN2 Z) (MkFN Z)
failing "Can't solve constraint"
    w2 = Refl

w3 : Equal (FN3 Z) (MkFN Z)
failing "Can't solve constraint"
    w3 = Refl
