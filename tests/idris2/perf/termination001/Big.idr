total
foo : Nat -> (x, a0, a1, a2, a3, a4, a5, a6, a7 : a) -> Nat
foo  Z    x a0 a1 a2 a3 a4 a5 a6 a7 = 0
foo (S f) x a0 a1 a2 a3 a4 a5 a6 a7
  = foo f a0 x  a1 a2 a3 a4 a5 a6 a7
  + foo f a1 a0 x  a2 a3 a4 a5 a6 a7
  + foo f a2 a0 a1 x  a3 a4 a5 a6 a7
  + foo f a3 a0 a1 a2 x  a4 a5 a6 a7
  + foo f a4 a0 a1 a2 a3 x  a5 a6 a7
  + foo f a5 a0 a1 a2 a3 a4 x  a6 a7
  + foo f a6 a0 a1 a2 a3 a4 a5 x  a7
  + foo f a7 a0 a1 a2 a3 a4 a5 a6 x
