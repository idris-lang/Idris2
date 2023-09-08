module Lib1

infixr 5 %%%

export
(%%%) : Nat -> Nat -> Nat
m %%% n = minus m n
