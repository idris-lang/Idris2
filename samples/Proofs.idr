fiveIsFive : 5 = 5
fiveIsFive = Refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

-- twoPlusTwoBad : 2 + 2 = 5
-- twoPlusTwoBad = Refl

disjoint : (n : Nat) -> Z = S n -> Void
disjoint n prf = replace {p = disjointTy} prf ()
  where
    disjointTy : Nat -> Type
    disjointTy Z = ()
    disjointTy (S k) = Void

plusReduces : (n:Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesR : (n:Nat) -> plus n Z = n
plusReducesR n = Refl

plusReducesZ : (n:Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong S (plusReducesZ k)

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong S (plusReducesS k m)
