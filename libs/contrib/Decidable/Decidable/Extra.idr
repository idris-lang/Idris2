module Decidable.Decidable.Extra

import Data.Rel
import Data.Fun
import Data.Vect
import Data.HVect
import Data.Fun.Extra
import Decidable.Decidable

public export
NotNot : {n : Nat} -> {ts : Vect n Type} -> (r : Rel ts) -> Rel ts
NotNot r = map @{Nary} (Not . Not) r 

[DecidablePartialApplication] {x : t} -> (tts : Decidable (t :: ts) r) => Decidable ts (r x) where
  decide = decide @{tts} x

public export
doubleNegationElimination : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable ts r =>
  (witness : HVect ts) -> 
  uncurry (NotNot {ts} r) witness -> 
  uncurry              r  witness
doubleNegationElimination {ts = []     } @{dec} [] prfnn = 
  case decide @{dec} of
    Yes prf   => prf
    No  prfn => absurd $ prfnn prfn
doubleNegationElimination {ts = t :: ts} @{dec} (w :: witness) prfnn = 
  doubleNegationElimination {ts} {r = r w} @{ DecidablePartialApplication @{dec} } witness prfnn

doubleNegationForall : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable ts r =>
  All ts (NotNot {ts} r) -> All ts r
doubleNegationForall @{dec} forall_prf = 
  let prfnn : (witness : HVect ts) -> uncurry (NotNot {ts} r) witness
      prfnn = uncurryAll forall_prf
      prf   : (witness : HVect ts) -> uncurry              r  witness
      prf witness = doubleNegationElimination @{dec} witness (prfnn witness)
  in curryAll prf

public export
doubleNegationExists : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable ts r =>
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

