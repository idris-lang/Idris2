module Data.Fin

import public Data.Maybe
import Data.Nat
import Decidable.Equality

%default total

||| Numbers strictly less than some bound.  The name comes from "finite sets".
|||
||| It's probably not a good idea to use `Fin` for arithmetic, and they will be
||| exceedingly inefficient at run time.
||| @ n the upper bound
public export
data Fin : (n : Nat) -> Type where
    FZ : Fin (S k)
    FS : Fin k -> Fin (S k)

export
Uninhabited (Fin Z) where
  uninhabited FZ impossible
  uninhabited (FS f) impossible

export
Uninhabited (FZ = FS k) where
  uninhabited Refl impossible

export
Uninhabited (FS k = FZ) where
  uninhabited Refl impossible

export
fsInjective : FS m = FS n -> m = n
fsInjective Refl = Refl

export
Eq (Fin n) where
    (==) FZ FZ = True
    (==) (FS k) (FS k') = k == k'
    (==) _ _ = False

||| Convert a Fin to a Nat
public export
finToNat : Fin n -> Nat
finToNat FZ = Z
finToNat (FS k) = S $ finToNat k

||| `finToNat` is injective
export
finToNatInjective : (fm : Fin k) -> (fn : Fin k) -> (finToNat fm) = (finToNat fn) -> fm = fn
finToNatInjective FZ     FZ     _    = Refl
finToNatInjective (FS _) FZ     Refl impossible
finToNatInjective FZ     (FS _) Refl impossible
finToNatInjective (FS m) (FS n) prf  =
  cong FS $ finToNatInjective m n $ succInjective (finToNat m) (finToNat n) prf

export
Cast (Fin n) Nat where
    cast = finToNat

||| Convert a Fin to an Integer
public export
finToInteger : Fin n -> Integer
finToInteger FZ     = 0
finToInteger (FS k) = 1 + finToInteger k

export
Cast (Fin n) Integer where
    cast = finToInteger

||| Weaken the bound on a Fin by 1
public export
weaken : Fin n -> Fin (S n)
weaken FZ     = FZ
weaken (FS k) = FS $ weaken k

||| Weaken the bound on a Fin by some amount
public export
weakenN : (n : Nat) -> Fin m -> Fin (m + n)
weakenN n FZ = FZ
weakenN n (FS f) = FS $ weakenN n f

||| Weaken the bound on a Fin using a constructive comparison
public export
weakenLTE : Fin n -> LTE n m -> Fin m
weakenLTE  FZ     LTEZero impossible
weakenLTE (FS _)  LTEZero impossible
weakenLTE  FZ    (LTESucc _) = FZ
weakenLTE (FS x) (LTESucc y) = FS $ weakenLTE x y

||| Attempt to tighten the bound on a Fin.
||| Return `Left` if the bound could not be tightened, or `Right` if it could.
export
strengthen : {n : _} -> Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S _} FZ = Right FZ
strengthen {n = S _} (FS i) with (strengthen i)
  strengthen (FS _) | Left x  = Left $ FS x
  strengthen (FS _) | Right x = Right $ FS x
strengthen f = Left f

||| Add some natural number to a Fin, extending the bound accordingly
||| @ n the previous bound
||| @ m the number to increase the Fin by
public export
shift : (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift (S m) f = FS $ shift m f

||| The largest element of some Fin type
public export
last : {n : _} -> Fin (S n)
last {n=Z} = FZ
last {n=S _} = FS last

export
Ord (Fin n) where
  compare  FZ     FZ    = EQ
  compare  FZ    (FS _) = LT
  compare (FS _)  FZ    = GT
  compare (FS x) (FS y) = compare x y

public export
natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S _) = Just FZ
natToFin (S k) (S j)
    = case natToFin k j of
           Just k' => Just (FS k')
           Nothing => Nothing
natToFin _ _ = Nothing

||| Convert an `Integer` to a `Fin`, provided the integer is within bounds.
||| @n The upper bound of the Fin
public export
integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x Z = Nothing -- make sure 'n' is concrete, to save reduction!
integerToFin x n = if x >= 0 then natToFin (fromInteger x) n else Nothing

||| Allow overloading of Integer literals for Fin.
||| @ x the Integer that the user typed
||| @ prf an automatically-constructed proof that `x` is in bounds
public export
fromInteger : (x : Integer) -> {n : Nat} ->
              {auto prf : (IsJust (integerToFin x n))} ->
              Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

||| Convert an Integer to a Fin in the required bounds/
||| This is essentially a composition of `mod` and `fromInteger`
public export
restrict : (n : Nat) -> Integer -> Fin (S n)
restrict n val = let val' = assert_total (abs (mod val (cast (S n)))) in
                     -- reasoning about primitives, so we need the
                     -- 'believe_me'. It's fine because val' must be
                     -- in the right range
                     fromInteger {n = S n} val'
                         {prf = believe_me {a=IsJust (Just val')} ItIsJust}

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

export
DecEq (Fin n) where
  decEq FZ FZ = Yes Refl
  decEq FZ (FS f) = No absurd
  decEq (FS f) FZ = No absurd
  decEq (FS f) (FS f')
      = case decEq f f' of
             Yes p => Yes $ cong FS p
             No p => No $ p . fsInjective
