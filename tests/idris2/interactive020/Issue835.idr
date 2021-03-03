module Issue835

baz : (x : Nat) -> {P2 : Nat -> Type} -> P2 x
baz x = ?rhs3

foo : {P : Nat -> Type}  -> Dec (P 0)
foo = ?rhs1 where


  bar : {P2 : Nat -> Type} ->
          (x : Nat)
          -> P2 x
  bar x with (S x)
     bar x | x1 =  ?rhs2
