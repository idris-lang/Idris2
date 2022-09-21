module Data.Fin

import Control.Function
import public Control.Ord
import Data.List1
import public Data.Maybe
import public Data.Nat
import public Data.So
import Decidable.Equality.Core

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

||| Coerce between Fins with equal indices
public export
coerce : {n : Nat} -> (0 eq : m = n) -> Fin m -> Fin n -- TODO: make linear
coerce {n = S _} eq FZ = FZ
coerce {n = Z} eq FZ impossible
coerce {n = S _} eq (FS k) = FS (coerce (injective eq) k)
coerce {n = Z} eq (FS k) impossible

%transform "coerce-identity" coerce eq k = replace {p = Fin} eq k

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
Uninhabited (n = m) => Uninhabited (FS n = FS m) where
  uninhabited Refl @{nm} = uninhabited Refl @{nm}

export
Injective FS where
  injective Refl = Refl

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

finToNatInjective : (fm : Fin k) -> (fn : Fin k) -> (finToNat fm) = (finToNat fn) -> fm = fn
finToNatInjective FZ     FZ     _    = Refl
finToNatInjective (FS _) FZ     Refl impossible
finToNatInjective FZ     (FS _) Refl impossible
finToNatInjective (FS m) (FS n) prf  =
  cong FS $ finToNatInjective m n $ injective prf

||| `finToNat` is injective
export
Injective Fin.finToNat where
 injective = (finToNatInjective _ _)

export
Cast (Fin n) Nat where
    cast = finToNat

||| Convert a Fin to an Integer
public export
finToInteger : Fin n -> Integer
finToInteger FZ     = 0
finToInteger (FS k) = 1 + finToInteger k

-- %builtin NaturalToInteger Data.Fin.finToInteger

export
Show (Fin n) where
  show = show . finToInteger

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
weakenN : (0 n : Nat) -> Fin m -> Fin (m + n)
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
||| Return the tightened bound if there is one, else nothing.
export
strengthen : {n : _} -> Fin (S n) -> Maybe (Fin n)
strengthen {n = S _} FZ = Just FZ
strengthen {n = S _} (FS p) with (strengthen p)
  strengthen (FS _) | Nothing = Nothing
  strengthen (FS _) | Just q  = Just $ FS q
strengthen _ = Nothing

||| Add some natural number to a Fin, extending the bound accordingly
||| @ n the previous bound
||| @ m the number to increase the Fin by
public export
shift : (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift (S m) f = FS $ shift m f

||| Increment a Fin, wrapping on overflow
public export
finS : {n : Nat} -> Fin n -> Fin n
finS {n = S _} x = case strengthen x of
    Nothing => FZ
    Just y => FS y

||| The largest element of some Fin type
public export
last : {n : _} -> Fin (S n)
last {n=Z} = FZ
last {n=S _} = FS last

||| The finite complement of some Fin.
||| The number as far along as the input, but starting from the other end.
public export
complement : {n : Nat} -> Fin n -> Fin n
complement {n = S _} FZ = last
complement {n = S _} (FS x) = weaken $ complement x

||| All of the Fin elements
public export
allFins : (n : Nat) -> List1 (Fin (S n))
allFins Z = FZ ::: []
allFins (S n) = FZ ::: map FS (forget (allFins n))

export
Ord (Fin n) where
  compare  FZ     FZ    = EQ
  compare  FZ    (FS _) = LT
  compare (FS _)  FZ    = GT
  compare (FS x) (FS y) = compare x y

namespace Monoid

  public export
  [Minimum] {n : Nat} -> Monoid (Fin $ S n) using Semigroup.Minimum where
    neutral = last

  public export
  [Maximum] Monoid (Fin $ S n) using Semigroup.Maximum where
    neutral = FZ

public export
natToFinLT : (x : Nat) -> {0 n : Nat} ->
             {auto 0 prf : x `LT` n} ->
             Fin n
natToFinLT Z {prf = LTESucc _} = FZ
natToFinLT (S k) {prf = LTESucc _} = FS $ natToFinLT k

public export
natToFinLt : (x : Nat) -> {n : Nat} ->
             {auto 0 prf : So (x < n)} ->
             Fin n
natToFinLt Z     {n = S _} = FZ
natToFinLt (S k) {n = S _} = FS $ natToFinLt k

public export
natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin x n = case isLT x n of
    Yes prf => Just $ natToFinLT x
    No contra => Nothing

||| Convert an `Integer` to a `Fin`, provided the integer is within bounds.
||| @n The upper bound of the Fin
public export
integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x Z = Nothing -- make sure 'n' is concrete, to save reduction!
integerToFin x n = if x >= 0 then natToFin (fromInteger x) n else Nothing

public export
maybeLTE : (x : Nat) -> (y : Nat) -> Maybe (x `LTE` y)
maybeLTE Z _ = Just LTEZero
maybeLTE (S x) (S y) = LTESucc <$> maybeLTE x y
maybeLTE _ _ = Nothing

public export
maybeLT : (x : Nat) -> (y : Nat) -> Maybe (x `LT` y)
maybeLT x y = maybeLTE (S x) y

public export
finFromInteger : (x : Integer) -> {n : Nat} ->
                 {auto 0 prf : So (fromInteger x < n)} ->
                 Fin n
finFromInteger x = natToFinLt (fromInteger x)

-- Direct comparison between `Integer` and `Nat`.
-- We cannot convert the `Nat` to `Integer`, because that will not work with open terms;
-- but we cannot convert the `Integer` to `Nat` either, because that slows down typechecking
-- even when the function is unused (issue #2032)
public export
integerLessThanNat : Integer -> Nat -> Bool
integerLessThanNat x n with (x < the Integer 0)
  integerLessThanNat _ _     | True  = True                            -- if `x < 0` then `x < n` for any `n : Nat`
  integerLessThanNat x (S m) | False = integerLessThanNat (x-1) m      -- recursive case
  integerLessThanNat x Z     | False = False                           -- `x >= 0` contradicts `x < Z`

||| Allow overloading of Integer literals for Fin.
||| @ x the Integer that the user typed
||| @ prf an automatically-constructed proof that `x` is in bounds
public export
fromInteger : (x : Integer) -> {n : Nat} ->
              {auto 0 prf : So (integerLessThanNat x n)} ->
              Fin n
fromInteger x = finFromInteger x {prf = lemma prf} where
  -- to be minimally invasive, we just call the previous implementation.
  -- however, having a different proof obligation resolves #2032
  0 lemma : {x : Integer} -> {n : Nat} -> So (integerLessThanNat x n) -> So (fromInteger {ty=Nat} x < n)
  lemma oh = believe_me oh

-- %builtin IntegerToNatural Data.Fin.fromInteger

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
-- Num
--------------------------------------------------------------------------------

public export
{n : Nat} -> Num (Fin (S n)) where
  FZ + y = y
  (+) {n = S _} (FS x) y = finS $ assert_smaller x (weaken x) + y

  FZ * y = FZ
  (FS x) * y = y + (assert_smaller x $ weaken x) * y

  fromInteger = restrict n

public export
{n : Nat} -> Neg (Fin (S n)) where
  negate = finS . complement

  x - y = x + (negate y)

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

public export
DecEq (Fin n) where
  decEq FZ FZ = Yes Refl
  decEq (FS f) (FS f') = decEqCong $ decEq f f'
  decEq FZ (FS f) = No absurd
  decEq (FS f) FZ = No absurd

namespace Equality

  ||| Pointwise equality of Fins
  ||| It is sometimes complicated to prove equalities on type-changing
  ||| operations on Fins.
  ||| This inductive definition can be used to simplify proof. We can
  ||| recover proofs of equalities by using `homoPointwiseIsEqual`.
  public export
  data Pointwise : Fin m -> Fin n -> Type where
    FZ : Pointwise FZ FZ
    FS : Pointwise k l -> Pointwise (FS k) (FS l)

  infix 6 ~~~
  ||| Convenient infix notation for the notion of pointwise equality of Fins
  public export
  (~~~) : Fin m -> Fin n -> Type
  (~~~) = Pointwise

  ||| Pointwise equality is reflexive
  export
  reflexive : {k : Fin m} -> k ~~~ k
  reflexive {k = FZ} = FZ
  reflexive {k = FS k} = FS reflexive

  ||| Pointwise equality is symmetric
  export
  symmetric : k ~~~ l -> l ~~~ k
  symmetric FZ = FZ
  symmetric (FS prf) = FS (symmetric prf)

  ||| Pointwise equality is transitive
  export
  transitive : j ~~~ k -> k ~~~ l -> j ~~~ l
  transitive FZ FZ = FZ
  transitive (FS prf) (FS prg) = FS (transitive prf prg)

  ||| Pointwise equality is compatible with coerce
  export
  coerceEq : {k : Fin m} -> (0 eq : m = n) -> coerce eq k ~~~ k
  coerceEq {k = FZ} Refl = FZ
  coerceEq {k = FS k} Refl = FS (coerceEq _)

  ||| The actual proof used by coerce is irrelevant
  export
  congCoerce : {0 n, q : Nat} -> {k : Fin m} -> {l : Fin p} ->
               {0 eq1 : m = n} -> {0 eq2 : p = q} ->
               k ~~~ l ->
               coerce eq1 k ~~~ coerce eq2 l
  congCoerce eq
    = transitive (coerceEq _)
    $ transitive eq $ symmetric $ coerceEq _

  ||| Last is congruent wrt index equality
  export
  congLast : {m : Nat} -> (0 _ : m = n) -> last {n=m} ~~~ last {n}
  congLast Refl = reflexive

  export
  congShift : (m : Nat) -> k ~~~ l -> shift m k ~~~ shift m l
  congShift Z prf = prf
  congShift (S m) prf = FS (congShift m prf)

  ||| WeakenN is congruent wrt pointwise equality
  export
  congWeakenN : k ~~~ l -> weakenN n k ~~~ weakenN n l
  congWeakenN FZ = FZ
  congWeakenN (FS prf) = FS (congWeakenN prf)

  ||| Pointwise equality is propositional equality on Fins that have the same type
  export
  homoPointwiseIsEqual : {0 k, l : Fin m} -> k ~~~ l -> k === l
  homoPointwiseIsEqual FZ = Refl
  homoPointwiseIsEqual (FS prf) = cong FS (homoPointwiseIsEqual prf)

  ||| Pointwise equality is propositional equality modulo transport on Fins that
  ||| have provably equal types
  export
  hetPointwiseIsTransport :
     {0 k : Fin m} -> {0 l : Fin n} ->
     (0 eq : m === n) -> k ~~~ l -> k === rewrite eq in l
  hetPointwiseIsTransport Refl = homoPointwiseIsEqual

  export
  finToNatQuotient : k ~~~ l -> finToNat k === finToNat l
  finToNatQuotient FZ = Refl
  finToNatQuotient (FS prf) = cong S (finToNatQuotient prf)

  ||| Propositional equality on `finToNat`s implies pointwise equality on the `Fin`s themselves
  export
  finToNatEqualityAsPointwise : (k : Fin m) ->
                                (l : Fin n) ->
                                finToNat k = finToNat l ->
                                k ~~~ l
  finToNatEqualityAsPointwise FZ FZ _ = FZ
  finToNatEqualityAsPointwise FZ (FS _) prf = absurd prf
  finToNatEqualityAsPointwise (FS _) FZ prf = absurd prf
  finToNatEqualityAsPointwise (FS k) (FS l) prf = FS $ finToNatEqualityAsPointwise k l (injective prf)

  export
  weakenNeutral : (k : Fin n) -> weaken k ~~~ k
  weakenNeutral FZ = FZ
  weakenNeutral (FS k) = FS (weakenNeutral k)

  export
  weakenNNeutral : (0 m : Nat) -> (k : Fin n) -> weakenN m k ~~~ k
  weakenNNeutral m FZ = FZ
  weakenNNeutral m (FS k) = FS (weakenNNeutral m k)
