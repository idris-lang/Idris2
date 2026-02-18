View : Type -> Type
View a = a -> Type

-- Pre-image view
data (.inv) : (f : a -> b) -> View b where
  Choose : (x : a) -> f.inv (f x)

LessThanOrEqualTo : Nat -> Nat -> Type
LessThanOrEqualTo n k = (+n).inv k

Ex1 : 3 `LessThanOrEqualTo` 5
Ex1 = Choose 2

Bug : Not (3 `LessThanOrEqualTo` 5)
Bug Refl impossible

Yikes : Void
Yikes = Bug Ex1
