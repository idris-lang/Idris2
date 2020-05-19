import Control.Monad.Identity

public export
interface Foo (sA : Type) where
  A : Type
  Elem : A -> sA -> Type
  Empty : sA -> Type
  Empty as = (a : A) -> Not (Elem a as)

public export
implementation Foo (Identity Bool) where
  A = Bool
  Elem x (Id y) = x = y
