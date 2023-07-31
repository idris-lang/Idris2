%logging "declare.record.parameters" 60

-- used to fail with:
-- While processing type of .prf. Can't solve constraint between: ?a [no locals in scope] and rec .a.

record HasLength (xs : List a) (n : Nat) where
  constructor MkHasLength
  0 prf : length xs === n

data Vect : Type -> Nat -> Type where

record Harder (eq : xs === ys) (zs : Vect a n) (eq2 : zs === xs) where


parameters {a, b : Type}

  Product : Type
  Product = (a, b)

  record EtaProof (p : Product) where
    0 eta : p === (fst p, snd p)
