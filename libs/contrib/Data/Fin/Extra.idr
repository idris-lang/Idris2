module Data.Fin.Extra

import Data.Fin
import public Data.Fin.Arith as Data.Fin.Extra
import public Data.Fin.Properties as Data.Fin.Extra
import public Data.Fin.Split as Data.Fin.Extra
import Data.Nat
import Data.Nat.Division

import Syntax.WithProof
import Syntax.PreorderReasoning

%default total

-------------------------------------------------
--- Inversion function and related properties ---
-------------------------------------------------

-- These deprecated functions are to be removed as soon as 0.8.0 is released.

%deprecate -- Use `Data.Fin.complement` instead
public export %inline
invFin : {n : Nat} -> Fin n -> Fin n
invFin = complement

%deprecate -- Use `Data.Fin.Properties.complementSpec` instead
export %inline
invFinSpec : {n : _} -> (i : Fin n) -> 1 + finToNat i + finToNat (complement i) = n
invFinSpec = complementSpec

%deprecate -- Use `Data.Fin.Properties.complementWeakenIsFS` instead
export %inline
invFinWeakenIsFS : {n : Nat} -> (m : Fin n) -> complement (weaken m) = FS (complement m)
invFinWeakenIsFS = complementWeakenIsFS

%deprecate -- Use `Data.Fin.Properties.complementLastIsFZ` instead
export %inline
invFinLastIsFZ : {n : Nat} -> complement (last {n}) = FZ
invFinLastIsFZ = complementLastIsFZ

%deprecate -- Use `Data.Fin.Properties.complementInvolutive` instead
export %inline
invFinInvolutive : {n : Nat} -> (m : Fin n) -> complement (complement m) = m
invFinInvolutive = complementInvolutive

-----------------------------------
--- Division-related properties ---
-----------------------------------

||| A view of Nat as a quotient of some number and a finite remainder.
public export
data FractionView : (n : Nat) -> (d : Nat) -> Type where
    Fraction : (n : Nat) -> (d : Nat) -> {auto ok: GT d Z} ->
                (q : Nat) -> (r : Fin d) ->
                q * d + finToNat r = n -> FractionView n d

||| Converts Nat to the fractional view with a non-zero divisor.
export
divMod : (n, d : Nat) -> {auto ok: GT d Z} -> FractionView n d
divMod Z (S d) = Fraction Z (S d) Z FZ Refl
divMod {ok=_} (S n) (S d) =
    let Fraction {ok=ok} n (S d) q r eq = divMod n (S d) in
    case strengthen' r of
        Left eq' => Fraction {ok=ok} (S n) (S d) (S q) FZ $
            rewrite sym eq in
                rewrite trans (cong finToNat eq') finToNatLastIsBound in
                    cong S $ trans
                        (plusZeroRightNeutral (d + q * S d))
                        (plusCommutative d (q * S d))
        Right (r' ** eq') => Fraction {ok=ok} (S n) (S d) q (FS r') $
            rewrite sym $ plusSuccRightSucc (q * S d) (finToNat r') in
                cong S $ trans (sym $ cong (plus (q * S d)) eq') eq

||| Compute n % m as a Fin with upper bound m.
|||
||| Useful, for example, when iterating through a large index, computing
||| subindices as a function of the larger index (e.g. a flattened 2D-array)
export
modFin :  (n : Nat)
       -> (m : Nat)
       -> {auto mNZ : NonZero m}
       -> Fin m
modFin n 0 impossible
modFin 0 (S k) = FZ
modFin (S j) (S k) =
  let n' : Nat
      n' = modNatNZ (S j) (S k) mNZ in
  let ok = boundModNatNZ (S j) (S k) mNZ
  in natToFinLT n' @{ok}

||| Tighten the bound on a Fin by taking its current bound modulo the given
||| non-zero number.
export
strengthenMod :  {n : _}
             -> Fin n
             -> (m : Nat)
             -> {auto mNZ : NonZero m}
             -> Fin m
strengthenMod _ Z impossible
strengthenMod {n = 0} f m@(S k) = weakenN m f
strengthenMod {n = (S j)} f m@(S k) =
 let n' : Nat
     n' = modNatNZ (S j) (S k) %search in
 let ok = boundModNatNZ (S j) (S k) %search
 in natToFinLT n' @{ok}

-------------------
--- Conversions ---
-------------------

||| Total function to convert a nat to a Fin, given a proof
||| that it is less than the bound.
public export
natToFinLTE : (n : Nat) -> (0 _ : LT n m) -> Fin m
natToFinLTE Z     (LTESucc _) = FZ
natToFinLTE (S k) (LTESucc l) = FS $ natToFinLTE k l

||| Converting from a Nat to a Fin and back is the identity.
public export
natToFinToNat :
  (n : Nat)
  -> (lte : LT n m)
  -> finToNat (natToFinLTE n lte) = n
natToFinToNat 0 (LTESucc lte) = Refl
natToFinToNat (S k) (LTESucc lte) = cong S (natToFinToNat k lte)
