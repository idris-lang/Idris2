%logging "declare.record.parameters" 50

-- used to fail with:
-- While processing type of .prf. Can't solve constraint between: ?a [no locals in scope] and rec .a.

record HasLength (xs : List a) (n : Nat) where
  constructor MkHasLength
  0 prf : length xs === n

data Vect : Type -> Nat -> Type where

record Harder (eq : xs === ys) (zs : Vect a n) (eq2 : zs === xs) where
