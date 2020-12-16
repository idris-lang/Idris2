module Decidable.Decidable.Extra

import Data.Rel
import Data.Rel.Extra
import Data.Fun
import Data.Vect
import Data.HVect
import Data.Fun.Extra
import Decidable.Decidable

%default total


public export
NotNot : {n : Nat} -> {ts : Vect n Type} -> (r : Rel ts) -> Rel ts
NotNot r = map @{Nary} (Not . Not) r

[DecidablePartialApplication] {x : t} -> (tts : Decidable (S n) (t :: ts) r) => Decidable n ts (r x) where
  decide = decide @{tts} x

public export
doubleNegationElimination : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable n ts r =>
  (witness : HVect ts) ->
  uncurry (NotNot {ts} r) witness ->
  uncurry              r  witness
doubleNegationElimination {ts = []     } @{dec} [] prfnn =
  case decide @{dec} of
    Yes prf   => prf
    No  prfn => absurd $ prfnn prfn
doubleNegationElimination {ts = t :: ts} @{dec} (w :: witness) prfnn =
  doubleNegationElimination {ts} {r = r w} @{ DecidablePartialApplication @{dec} } witness prfnn

doubleNegationForall : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable n ts r =>
  All ts (NotNot {ts} r) -> All ts r
doubleNegationForall @{dec} forall_prf =
  let prfnn : (witness : HVect ts) -> uncurry (NotNot {ts} r) witness
      prfnn = uncurryAll forall_prf
      prf   : (witness : HVect ts) -> uncurry              r  witness
      prf witness = doubleNegationElimination @{dec} witness (prfnn witness)
  in curryAll prf

public export
doubleNegationExists : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable n ts r =>
  Ex ts (NotNot {ts} r) ->
  Ex ts r
doubleNegationExists {ts} {r} @{dec} nnxs =
  let witness : HVect ts
      witness = extractWitness nnxs
      witnessingnn : uncurry (NotNot {ts} r) witness
      witnessingnn = extractWitnessCorrect nnxs
      witnessing   : uncurry              r  witness
      witnessing   = doubleNegationElimination @{dec} witness witnessingnn
  in introduceWitness witness witnessing


||| Convert a decision about a decidable property into one about its negation.
public export
negateDec : (1 dec : Dec a) -> Dec (Not a)
negateDec (Yes pf) = No ($ pf)
negateDec (No npf) = Yes npf


[DecidableComplement] {ts : Vect n Type} -> {r : Rel ts} -> (posDec : Decidable n ts r) =>
  Decidable n ts (complement {ts} r) where
    decide {ts = []} = negateDec $ decide @{posDec}
    decide {ts = (t :: ts)} =
      \x =>
        let
          pd = DecidablePartialApplication {x = x} @{posDec}
          inst = DecidableComplement @{pd}
        in decide @{inst}
