import Data.Vect
import Data.Nat

export
lemmaPlusOneRight : (n : Nat) -> n + 1 = S n
lemmaPlusOneRight n = rewrite plusCommutative n 1 in Refl

public export
consLin : (1 _ : Unit) -> (1 _ : Vect n Unit) -> Vect (S n) Unit
consLin () [] = [()]
consLin () (x :: xs) = () :: x :: xs

consNonLin : Unit -> Vect n Unit -> Vect (n+1) Unit
consNonLin u us = rewrite lemmaPlusOneRight n in u `consLin` us

consLin2 : (1 _ : Unit) -> (1 _ : Vect n Unit) -> Vect (n+1) Unit
consLin2 u us = rewrite lemmaPlusOneRight n in u `consLin` us


