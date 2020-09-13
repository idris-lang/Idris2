module Decidable.Decidable.Extra

import Data.Rel
import Data.Fun
import Data.Vect
import Data.Fun.Extra
import Decidable.Decidable

public export
NotNot : {ts : Vect n Type} -> (r : Rel ts) -> Rel ts
NotNot r = map @{Nary} (Not . Not) r 

[DecidablePartialApplication] {x : t} -> (tts : Decidable (t :: ts) r) => Decidable ts (r x) where
  decide = decide @{tts} x

public export
doubleNegation : {ts : Vect n Type} -> {r : Rel ts} -> Decidable ts r =>
  Ex ts (NotNot {ts} r) -> 
  Ex ts r
doubleNegation {ts = []} @{dec} nnxs = case decide @{dec} of 
  Yes prf => prf
  No  not => absurd (nnxs not)
doubleNegation {ts = (t :: ts)} @{dec} (x ** nnxs) = 
  (x ** doubleNegation {ts} {r = r x} @{ DecidablePartialApplication @{dec} } nnxs)
 
