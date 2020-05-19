module Nat

public export
data Nat = Z | S Nat

public export
plus : Nat -> Nat -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

