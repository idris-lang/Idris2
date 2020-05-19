module Mult

import public Nat

public export
mult : Nat -> Nat -> Nat
mult Z y = Z
mult (S k) y = plus y (mult k y)
