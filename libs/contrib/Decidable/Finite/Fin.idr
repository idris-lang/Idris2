module Decidable.Finite.Fin

import Data.Nat
import Data.Nat.Order
import Data.Fin
import Decidable.Decidable.Extra
import Data.Fin.Extra

-- Private record type, storing a Fin with an irrelevant proof that it is bounded,
-- along with a proof that it matches some predicate.
record BoundedEx {n : Nat} (bound : Nat) (P : Fin n -> Type) where
  constructor BndEx
  {bndWitness : Fin n}
  0 bndLTE : LTE (finToNat bndWitness) bound
  bndPf : P bndWitness

-- Private helper for the decidability of existential properties on Fin n.
-- The problem this helper solves is that pattern matching on (S k : Fin (S n))
-- gives (k : Fin n), so if we're proving a predicate (P : Fin (S n) -> Set),
-- we can't directly give it k.
-- Instead, we do induction on a natural-number bound for finite numbers
-- that is less than the bound given than the type.
-- The function shows that if we can decide whether a predicate holds for the biggest
-- number <= some bound, and recursively decide if it holds for any smaller numbers,
-- then we can decide if it holds for any number <= the bound.
boundedFiniteEx :
  {0 n : Nat}
  -> {P : Fin n -> Type}
  -> (bound : Nat)
  -> (boundBounded : LTE (S bound) n)
  -> (Dec  (P (natToFinLTE bound boundBounded)) )
  -> ((x : Fin n) -> Dec (P x))
  -> Dec (BoundedEx bound P)
boundedFiniteEx {n = n} bound boundBounded (Yes pf) ddec =
  Yes $ BndEx (rewrite natToFinToNat bound boundBounded in lteRefl) pf
boundedFiniteEx {n = S n1} 0 (LTESucc bounded)(No npf) ddec = No $ \bnd => helper (bndLTE bnd) (bndPf bnd)
  where
    -- Do the pattern matching to determine that only 0 <= 0
    helper : {x : Fin (S n1)} -> (0 _ : LTE (finToNat x) 0) -> P x -> Void
    helper {x = FZ} LTEZero pf = npf pf
boundedFiniteEx {n = S n1} (S bound') (LTESucc lte) (No npf) ddec with (boundedFiniteEx {  n = S n1} bound' (lteSuccRight lte) (ddec _) ddec)
  boundedFiniteEx {n = S n1} (S bound') (LTESucc lte) (No npf) ddec | Yes bnd =
      Yes $ BndEx (lteSuccRight $ bndLTE bnd) (bndPf bnd)
  boundedFiniteEx {n = S n1} (S bound') (LTESucc lte) (No npf) ddec | No rec =
    No \ bnd =>  void $ helper (bndLTE bnd) (bndPf bnd)
      where
        -- Use the decidability of LTE to show that a property holds
        -- for some number <= than a bound iff it holds
        -- for the bound, or for some number strictly less than the bound.
        helper : {x : Fin (S n1)} ->  LTE (finToNat x) (S bound') -> P x -> Void
        helper {x = x} xlte px with (isLTE (finToNat x) bound')
          helper {x = x} xlte px | Yes blte = rec $ BndEx blte px
          helper {x = x} xlte px | No nlt = npf $ (rewrite (sym eq) in px)
            where
              eq : x = (FS $ natToFinLTE bound' lte)
              eq  = finToNatInjective _ _  $ trans (LTEIsAntisymmetric _ _  xlte (notLTEImpliesGT nlt)) $ cong S (sym $ natToFinToNat _ _)

||| Given a decidable predicate on Fin n,
||| it's decidable whether any numbers in Fin n satisfy it.
finiteDecEx :
  {n : Nat}
  -> {p : Fin n -> Type}
  -> ((x : Fin n) -> Dec (p x))
  -> Dec (x : Fin n ** p x)
finiteDecEx {n = 0} dec = No $ \ pr => absurd (fst pr)
finiteDecEx {n = (S n1)} dec
  with (boundedFiniteEx (finToNat last) (elemSmallerThanBound (last {n = n1})) (dec _) dec)
  finiteDecEx {n = (S n1)} dec | Yes bnd = Yes (bndWitness bnd ** bndPf bnd)
  finiteDecEx {n = (S n1)} dec | No nbnd = No $ \ pr => nbnd $ BndEx lessThanLast (snd pr)
    where
      lessThanLast : {x : Fin (S n1)} -> LTE (finToNat x) (finToNat (last {n = n1} ))
      lessThanLast {x} =
        rewrite finToNatLastIsBound {n = n1}
        in fromLteSucc $ elemSmallerThanBound x

||| Given a decidable predicate on Fin n,
||| it's decidable whether all numbers in Fin n satisfy it.
finiteDecAll :
  {n : Nat}
  -> {p : Fin n -> Type}
  -> ((x : Fin n)
  -> Dec (p x))
  -> Dec ((x : Fin n) -> p x)
finiteDecAll dec  = case finiteDecEx (\ x => negateDec $ dec x) of
    Yes ex => No $ \f => snd ex $ f $ fst ex
    No nex => Yes $ \x => case dec x of
      Yes pf => pf
      No npf => void $ nex (x ** npf)
