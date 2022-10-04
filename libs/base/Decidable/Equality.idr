module Decidable.Equality

import Control.Function
import Data.Maybe
import Data.Either
import Data.Nat
import Data.List
import Data.List1
import Data.List1.Properties
import Data.SnocList
import Data.These

import public Decidable.Equality.Core as Decidable.Equality

%default total

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

public export
DecEq () where
  decEq () () = Yes Refl

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------

public export
DecEq Bool where
  decEq True  True  = Yes Refl
  decEq False False = Yes Refl
  decEq False True  = No absurd
  decEq True  False = No absurd

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

public export
DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq (S n) (S m) = decEqCong $ decEq n m
  decEq Z     (S _) = No absurd
  decEq (S _) Z     = No absurd

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

public export
DecEq t => DecEq (Maybe t) where
  decEq Nothing Nothing = Yes Refl
  decEq (Just x) (Just y) = decEqCong $ decEq x y
  decEq Nothing (Just _) = No absurd
  decEq (Just _) Nothing = No absurd

--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

public export
(DecEq t, DecEq s) => DecEq (Either t s) where
  decEq (Left x)  (Left y)  = decEqCong $ decEq x y
  decEq (Right x) (Right y) = decEqCong $ decEq x y
  decEq (Left x) (Right y) = No absurd
  decEq (Right x) (Left y) = No absurd

--------------------------------------------------------------------------------
-- These (inclusive or)
--------------------------------------------------------------------------------

public export
DecEq t => DecEq s => DecEq (These t s) where
  decEq (This x) (This y) = decEqCong $ decEq x y
  decEq (That x) (That y) = decEqCong $ decEq x y
  decEq (Both x z) (Both y w) = decEqCong2 (decEq x y) (decEq z w)
  decEq (This x)   (That y)    = No $ \case Refl impossible
  decEq (This x)   (Both y z)  = No $ \case Refl impossible
  decEq (That x)   (This y)    = No $ \case Refl impossible
  decEq (That x)   (Both y z)  = No $ \case Refl impossible
  decEq (Both x z) (This y)    = No $ \case Refl impossible
  decEq (Both x z) (That y)    = No $ \case Refl impossible

--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

pairInjective : (a, b) = (c, d) -> (a = c, b = d)
pairInjective Refl = (Refl, Refl)

public export
(DecEq a, DecEq b) => DecEq (a, b) where
  decEq (a, b) (a', b') = decEqCong2 (decEq a a') (decEq b b')

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

public export
DecEq a => DecEq (List a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) [] = No absurd
  decEq [] (x :: xs) = No absurd
  decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)

--------------------------------------------------------------------------------
-- List1
--------------------------------------------------------------------------------

public export
DecEq a => DecEq (List1 a) where
  decEq (x ::: xs) (y ::: ys) = decEqCong2 (decEq x y) (decEq xs ys)

--------------------------------------------------------------------------------
-- SnocList
--------------------------------------------------------------------------------

public export
DecEq a => DecEq (SnocList a) where
  decEq Lin Lin = Yes Refl
  decEq (xs :< x) Lin = No absurd
  decEq Lin (xs :< x) = No absurd
  decEq (xs :< x) (ys :< y) = decEqCong2 (decEq xs ys) (decEq x y)

-- TODO: Other prelude data types

-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations. We use believe_me for the inequality proofs
-- because we don't them to reduce (and they should never be needed anyway...)
-- A postulate would be better, but erasure analysis may think they're needed
-- for computation in a higher order setting.


||| An unsafe decidable equality implementation based on boolean equality.
||| Useful for builtin types.
public export
[FromEq] Eq a => DecEq a where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

public export
DecEq Int where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits8
--------------------------------------------------------------------------------

public export
DecEq Bits8 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits16
--------------------------------------------------------------------------------

public export
DecEq Bits16 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits32
--------------------------------------------------------------------------------

public export
DecEq Bits32 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits64
--------------------------------------------------------------------------------

public export
DecEq Bits64 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int8
--------------------------------------------------------------------------------

public export
DecEq Int8 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int16
--------------------------------------------------------------------------------

public export
DecEq Int16 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int32
--------------------------------------------------------------------------------

public export
DecEq Int32 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int64
--------------------------------------------------------------------------------

public export
DecEq Int64 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Char
--------------------------------------------------------------------------------
public export
DecEq Char where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Integer
--------------------------------------------------------------------------------
public export
DecEq Integer where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- String
--------------------------------------------------------------------------------
public export
DecEq String where
    decEq = decEq @{FromEq}
