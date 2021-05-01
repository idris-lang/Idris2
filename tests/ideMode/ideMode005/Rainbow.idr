namespace L0
  public export
  data List0 : Type


namespace L1
  public export
  data List1 : Type where
    Nil : List1
    Cons1 : Nat -> List0 -> List1

  public export
  (::) : Nat -> List0 -> List1
  (::) = Cons1

namespace L2
  public export
  data (::) : Nat -> List0 -> Type where

namespace L0
  public export
  data List0 : Type where
    Nil : List0
    (::) : Nat ->Type -> List0

m : Nat
m = believe_me %MkWorld

Rainbow : Nat -> Type
Rainbow n =  [ n , m , n ]
