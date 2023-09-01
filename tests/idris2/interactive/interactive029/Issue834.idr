foo : {p,q  : Nat -> Type} -> p x
foo = ?a

  where

    helper : {p2 : Nat -> Nat -> Type} -> p2 y 0
    helper = ?b

    helper1 : {p2 : Nat -> Nat -> Type} -> (y : Nat) -> p2 y 0
    helper1 = ?c

    helper2 : (y : Nat) -> {p2 : Nat -> Nat -> Type} -> p2 y 0
    helper2 = ?d

    -- introduce the ones after explicitly bound variables though
    helper3 : (y : Nat) -> {p2 : Nat -> Nat -> Type} -> p2 y 0
    helper3 y = ?e
