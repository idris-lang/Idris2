module Implicit

%default total

%logging elab.generalise 20

mapId : (xs : List a) -> map id xs === xs
mapId [] = Refl
mapId (x :: xs) = cong (x ::) (mapId xs)

three : Nat
three = 3

threeIs3 : three === 3
threeIs3 = Refl

twiceFour : four === the Nat 4 -> (four + four) === 8
twiceFour Refl = Refl

lhsIsFine : Nat -> Nat
lhsIsFine id = id

withIsFine : Nat -> Nat
withIsFine n with (n + n)
  withIsFine n | twon = twon
