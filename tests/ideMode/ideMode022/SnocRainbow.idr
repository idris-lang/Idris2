namespace L0
  public export
  data List0 : Type


namespace L1
  public export
  data List1 : Type where
    Lin : List1
    Cons1 : List0 -> Nat -> List1

  public export
  (:<) : List0 -> Nat -> List1
  (:<) = Cons1

namespace L2
  public export
  data (:<) : List0 -> Nat -> Type where

namespace L0
  public export
  data List0 : Type where
    Lin : List0
    (:<) : Type -> Nat -> List0

m : Nat
m = believe_me %MkWorld

Rainbow : Nat -> Type
Rainbow n =  [< n , m , n ]
