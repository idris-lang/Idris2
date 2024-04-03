module Lib1

export infixr 5 %%%

export
(%%%) : Nat -> Nat -> Nat
m %%% n = minus m n
