total
foo : Nat -> (x, a0, a1, a2, a3, a4 : a) -> Nat
foo  Z    x a0 a1 a2 a3 a4 = 0
foo (S f) x a0 a1 a2 a3 a4
  = foo f a0 x a1 a2 a3 a4
  + foo f a1 a0 x a2 a3 a4
  + foo f a2 a0 a1 x a3 a4
  + foo f a3 a0 a1 a2 x a4
  + foo f a3 a0 a1 a2 a4 x
