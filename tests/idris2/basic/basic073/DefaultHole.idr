foo : (Nat -> {default 42 _ : Nat} -> Nat) -> Nat
foo f = f 0

bar : Nat
bar = foo baz
  where
  baz : Nat -> {default ? y : Nat} -> Nat
  baz x = x + y
