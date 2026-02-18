import Data.Vect

%logging "elab" 1

[Named] {n : Nat} -> Show (Vect n a) where
  show x = "whatever"
