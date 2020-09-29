module Decidable.Equality

import Data.Maybe
import Data.Either
import Data.Nat
import Data.List
import Data.List1

%default total

--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

||| Decision procedures for propositional equality
public export
interface DecEq t where
  ||| Decide whether two elements of `t` are propositionally equal
  decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

||| The negation of equality is symmetric (follows from symmetry of equality)
export
negEqSym : forall a, b . (a = b -> Void) -> (b = a -> Void)
negEqSym p h = p (sym h)

||| Everything is decidably equal to itself
export
decEqSelfIsYes : DecEq a => {x : a} -> decEq x x = Yes Refl
decEqSelfIsYes {x} with (decEq x x)
  decEqSelfIsYes {x} | Yes Refl = Refl
  decEqSelfIsYes {x} | No contra = absurd $ contra Refl

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

export
DecEq () where
  decEq () () = Yes Refl

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

export
DecEq Bool where
  decEq True  True  = Yes Refl
  decEq False False = Yes Refl
  decEq False True  = No absurd
  decEq True  False = No absurd

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

export
DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq Z     (S _) = No absurd
  decEq (S _) Z     = No absurd
  decEq (S n) (S m) with (decEq n m)
   decEq (S n) (S m) | Yes p = Yes $ cong S p
   decEq (S n) (S m) | No p = No $ \h : (S n = S m) => p $ succInjective n m h

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

export
DecEq t => DecEq (Maybe t) where
  decEq Nothing Nothing = Yes Refl
  decEq Nothing (Just _) = No absurd
  decEq (Just _) Nothing = No absurd
  decEq (Just x') (Just y') with (decEq x' y')
    decEq (Just x') (Just y') | Yes p = Yes $ cong Just p
    decEq (Just x') (Just y') | No p
       = No $ \h : Just x' = Just y' => p $ justInjective h

--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

Uninhabited (Left x = Right y) where
  uninhabited Refl impossible

Uninhabited (Right x = Left y) where
  uninhabited Refl impossible

export
(DecEq t, DecEq s) => DecEq (Either t s) where
  decEq (Left x) (Left y) with (decEq x y)
   decEq (Left x) (Left x) | Yes Refl = Yes Refl
   decEq (Left x) (Left y) | No contra = No (contra . leftInjective)
  decEq (Left x) (Right y) = No absurd
  decEq (Right x) (Left y) = No absurd
  decEq (Right x) (Right y) with (decEq x y)
   decEq (Right x) (Right x) | Yes Refl = Yes Refl
   decEq (Right x) (Right y) | No contra = No (contra . rightInjective)

--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

pairInjective : (a, b) = (c, d) -> (a = c, b = d)
pairInjective Refl = (Refl, Refl)

export
(DecEq a, DecEq b) => DecEq (a, b) where
  decEq (a, b) (a', b') with (decEq a a')
    decEq (a, b) (a', b') | (No contra) =
      No $ contra . fst . pairInjective
    decEq (a, b) (a, b') | (Yes Refl) with (decEq b b')
      decEq (a, b) (a, b) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (a, b) (a, b') | (Yes Refl) | (No contra) =
        No $ contra . snd . pairInjective

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

export
DecEq a => DecEq (List a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) [] = No absurd
  decEq [] (x :: xs) = No absurd
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (y :: ys) | No contra =
      No $ contra . fst . consInjective
    decEq (x :: xs) (x :: ys) | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No contra) =
        No $ contra . snd . consInjective


--------------------------------------------------------------------------------
-- List1
--------------------------------------------------------------------------------

export
DecEq a => DecEq (List1 a) where

  decEq (x ::: xs) (y ::: ys) with (decEq x y)
    decEq (x ::: xs) (y ::: ys) | No contra = No (contra . fst . consInjective)
    decEq (x ::: xs) (y ::: ys) | Yes eqxy with (decEq xs ys)
    decEq (x ::: xs) (y ::: ys) | Yes eqxy | No contra = No (contra . snd . consInjective)
    decEq (x ::: xs) (y ::: ys) | Yes eqxy | Yes eqxsys = Yes (cong2 (:::) eqxy eqxsys)

-- TODO: Other prelude data types

-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations. We use believe_me for the inequality proofs
-- because we don't them to reduce (and they should never be needed anyway...)
-- A postulate would be better, but erasure analysis may think they're needed
-- for computation in a higher order setting.


--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------
export
implementation DecEq Int where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . x = y -> Void
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Char
--------------------------------------------------------------------------------
export
implementation DecEq Char where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . x = y -> Void
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Integer
--------------------------------------------------------------------------------
export
implementation DecEq Integer where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . x = y -> Void
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------
export
implementation DecEq String where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . x = y -> Void
             primitiveNotEq prf = believe_me {b = Void} ()
