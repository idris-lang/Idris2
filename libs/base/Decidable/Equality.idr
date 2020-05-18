module Decidable.Equality

import Data.Maybe
import Data.Nat

--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

||| Decision procedures for propositional equality
public export
interface DecEq t where
  ||| Decide whether two elements of `t` are propositionally equal
  total decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

||| The negation of equality is symmetric (follows from symmetry of equality)
export total
negEqSym : forall a, b . (a = b -> Void) -> (b = a -> Void)
negEqSym p h = p (sym h)

||| Everything is decidably equal to itself
export total
decEqSelfIsYes : DecEq a => {x : a} -> decEq x x = Yes Refl
decEqSelfIsYes {x} with (decEq x x)
  decEqSelfIsYes {x} | Yes Refl = Refl
  decEqSelfIsYes {x} | No contra = absurd $ contra Refl

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

export
implementation DecEq () where
  decEq () () = Yes Refl

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------
total trueNotFalse : True = False -> Void
trueNotFalse Refl impossible

export
implementation DecEq Bool where
  decEq True  True  = Yes Refl
  decEq False False = Yes Refl
  decEq True  False = No trueNotFalse
  decEq False True  = No (negEqSym trueNotFalse)

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

total ZnotS : Z = S n -> Void
ZnotS Refl impossible

export
implementation DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq Z     (S _) = No ZnotS
  decEq (S _) Z     = No (negEqSym ZnotS)
  decEq (S n) (S m) with (decEq n m)
   decEq (S n) (S m) | Yes p = Yes $ cong S p
   decEq (S n) (S m) | No p = No $ \h : (S n = S m) => p $ succInjective n m h

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

total nothingNotJust : {x : t} -> (Nothing {ty = t} = Just x) -> Void
nothingNotJust Refl impossible

export
implementation (DecEq t) => DecEq (Maybe t) where
  decEq Nothing Nothing = Yes Refl
  decEq (Just x') (Just y') with (decEq x' y')
    decEq (Just x') (Just y') | Yes p = Yes $ cong Just p
    decEq (Just x') (Just y') | No p
       = No $ \h : Just x' = Just y' => p $ justInjective h
  decEq Nothing (Just _) = No nothingNotJust
  decEq (Just _) Nothing = No (negEqSym nothingNotJust)

-- TODO: Other prelude data types

-- For the primitives, we have to cheat because we don't have access to their
-- internal implementations. We use believe_me for the inequality proofs
-- because we don't them to reduce (and they should never be needed anyway...)
-- A postulate would be better, but erasure analysis may think they're needed
-- for computation in a higher order setting.

--------------------------------------------------------------------------------
-- Tuple
--------------------------------------------------------------------------------

lemma_both_neq : (x = x' -> Void) -> (y = y' -> Void) -> ((x, y) = (x', y') -> Void)
lemma_both_neq p_x_not_x' p_y_not_y' Refl = p_x_not_x' Refl

lemma_snd_neq : (x = x) -> (y = y' -> Void) -> ((x, y) = (x, y') -> Void)
lemma_snd_neq Refl p Refl = p Refl

lemma_fst_neq_snd_eq : (x = x' -> Void) ->
                       (y = y') ->
                       ((x, y) = (x', y) -> Void)
lemma_fst_neq_snd_eq p_x_not_x' Refl Refl = p_x_not_x' Refl

export
implementation (DecEq a, DecEq b) => DecEq (a, b) where
  decEq (a, b) (a', b')     with (decEq a a')
    decEq (a, b) (a, b')    | (Yes Refl) with (decEq b b')
      decEq (a, b) (a, b)   | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (a, b) (a, b')  | (Yes Refl) | (No p) = No (\eq => lemma_snd_neq Refl p eq)
    decEq (a, b) (a', b')   | (No p)     with (decEq b b')
      decEq (a, b) (a', b)  | (No p)     | (Yes Refl) =  No (\eq => lemma_fst_neq_snd_eq p Refl eq)
      decEq (a, b) (a', b') | (No p)     | (No p') = No (\eq => lemma_both_neq p p' eq)

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

lemma_val_not_nil : (the (List _) (x :: xs) = Prelude.Nil {a = t} -> Void)
lemma_val_not_nil Refl impossible

lemma_x_eq_xs_neq : (x = y) -> (xs = ys -> Void) -> (the (List _) (x :: xs) = (y :: ys) -> Void)
lemma_x_eq_xs_neq Refl p Refl = p Refl

lemma_x_neq_xs_eq : (x = y -> Void) -> (xs = ys) -> (the (List _) (x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_eq p Refl Refl = p Refl

lemma_x_neq_xs_neq : (x = y -> Void) -> (xs = ys -> Void) -> (the (List _) (x :: xs) = (y :: ys) -> Void)
lemma_x_neq_xs_neq p p' Refl = p Refl

implementation DecEq a => DecEq (List a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) [] = No lemma_val_not_nil
  decEq [] (x :: xs) = No (negEqSym lemma_val_not_nil)
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (x :: xs) (x :: ys) | Yes Refl with (decEq xs ys)
      decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (x :: xs) (x :: ys) | (Yes Refl) | (No p) = No (\eq => lemma_x_eq_xs_neq Refl p eq)
    decEq (x :: xs) (y :: ys) | No p with (decEq xs ys)
      decEq (x :: xs) (y :: xs) | (No p) | (Yes Refl) = No (\eq => lemma_x_neq_xs_eq p Refl eq)
      decEq (x :: xs) (y :: ys) | (No p) | (No p') = No (\eq => lemma_x_neq_xs_neq p p' eq)


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

