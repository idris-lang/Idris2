|||
|||
||| foldr is the unique solution to the equation:
|||
|||   h f e [] = e
|||   h f e (x :: xs) = x `h` (foldr f e xs)
|||
||| (This fact is called 'the universal property of foldr'.)
|||
||| Since the prelude defines foldr tail-recursively, this fact isn't immediate
||| and we need some lemmata to prove it.
module Data.Vect.Properties.Foldr

import Data.Vect
import Data.Vect.Elem
import Data.Fin
import Data.Nat

import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic

||| Sum implemented with foldr
public export
sumR : Num a => Foldable f => f a -> a
sumR = foldr (+) 0

%transform "sumR/sum" sumR = sum

||| A function H : forall n. Vect n A -> B preserving the structure of vectors over A
public export
record VectHomomorphismProperty {0 A, B : Type} (F : A -> B -> B) (E : B) (H : forall n . Vect n A -> B) where
  constructor ShowVectHomomorphismProperty
  nil  : H [] = E
  cons : {0 n : Nat} -> (x : A) -> (xs : Vect n A) -> H (x :: xs) = x `F` (H xs)

||| There is an extensionally unique function preserving the vector structure
export
nilConsInitiality :
     (f : a -> b -> b) -> (e : b)
  -> (h1, h2 : forall n . Vect n a -> b)
  -> (prf1 : VectHomomorphismProperty f e h1)
  -> (prf2 : VectHomomorphismProperty f e h2)
  -> (xs : Vect n a) -> h1 xs = h2 xs
nilConsInitiality f e h1 h2 prf1 prf2 [] = Calc $
  |~ h1 []
  ~~ e     ...(prf1.nil)
  ~~ h2 [] ...(sym prf2.nil)

nilConsInitiality f e h1 h2 prf1 prf2 (x :: xs) = Calc $
  |~ h1 (x :: xs)
  ~~ (x `f` (h1 xs)) ...(prf1.cons _ _)
  ~~ (x `f` (h2 xs)) ...(cong (x `f`) $ nilConsInitiality f e h1 h2 prf1 prf2 xs)
  ~~ h2 (x :: xs) ...(sym $ prf2.cons _ _)

||| extensionality is a congruence with respect to Data.Vect.foldrImpl
foldrImplExtensional :
  (f : a -> b -> b) -> (e : b)
  -> (go1, go2 : b -> b)
  -> ((y : b) -> go1 y = go2 y)
  -> (xs : Vect n a)
  -> foldrImpl f e go1 xs = foldrImpl f e go2 xs
foldrImplExtensional f e go1 go2 ext [] = ext e
foldrImplExtensional f e go1 go2 ext (x :: xs) =
  foldrImplExtensional f e _ _
  (\y => ext (f x y))
  xs

||| foldrImpl f e x : (b -> -) -> - is natural
foldrImplNaturality : (f : a -> b -> b) -> (e : b) -> (xs : Vect n a) -> (go1, go2 : b -> b)
  -> foldrImpl f e (go1 . go2) xs = go1 (foldrImpl f e go2 xs)
foldrImplNaturality f e    []     go1 go2 = Refl
foldrImplNaturality f e (x :: xs) go1 go2 = foldrImplNaturality f e xs go1 (go2 . (f x))

||| Our tail-recursive foldr preserves the vector structure
export
foldrVectHomomorphism : VectHomomorphismProperty f e (foldr f e)
foldrVectHomomorphism = ShowVectHomomorphismProperty
  { nil  = Refl
  , cons = \x, xs => Calc $
    |~ foldr f e (x :: xs)
    ~~ foldrImpl f e (id . (f x)) xs ...(Refl)
    ~~ foldrImpl f e ((f x) . id) xs ...(foldrImplExtensional f e _ _ (\y => Refl) xs)
    ~~ f x (foldrImpl f e id xs)     ...(foldrImplNaturality f e xs (f x) _)
    ~~ f x (foldr f e xs)            ...(Refl)
  }

||| foldr is the unique function preserving the vector structure
export
foldrUniqueness : (h : forall n . Vect n a -> b) -> VectHomomorphismProperty f e h -> (xs : Vect n a) -> h xs = foldr f e xs
foldrUniqueness {f} h prf xs = irrelevantEq $
  nilConsInitiality f e h (foldr f e) prf foldrVectHomomorphism xs


||| Each summand is `LTE` the sum
export
sumIsGTEtoParts : {x : Nat} -> (xs : Vect n Nat) -> (x `Elem` xs) -> sumR xs `GTE` x
sumIsGTEtoParts (x :: xs) Here
  = CalcWith $
  |~ x
  ~~ x + 0 ...(sym $ plusZeroRightNeutral _)
  <~ x + (sumR xs)   ...(plusLteMonotoneLeft x 0 _ LTEZero)
  ~~ sumR (x :: xs)  ...(sym $ (foldrVectHomomorphism {f = plus} {e = 0}).cons _ _)

sumIsGTEtoParts {x} (y :: xs) (There later)
  = CalcWith $
    |~ x
    <~ sumR xs       ...(sumIsGTEtoParts {x} xs later)
    ~~ 0 + sumR xs   ...(Refl)
    <~ y + (sumR xs) ...(plusLteMonotoneRight (sumR xs) 0 y LTEZero)
    ~~ sumR (y :: xs) ...(sym $ (foldrVectHomomorphism {f = plus} {e = 0}).cons _ _)

||| `sumR : Vect n Nat -> Nat` is monotone
export
sumMonotone : {n : Nat} -> (xs, ys : Vect n Nat)
  -> (prf : (i : Fin n) -> index i xs `LTE` index i ys)
  -> (sumR xs `LTE` sumR ys)
sumMonotone [] [] prf = LTEZero
sumMonotone (x :: xs) (y :: ys) prf =
  let prf' = sumMonotone xs ys (\i => prf (FS i))
  in CalcWith $
  |~ sumR (x :: xs)
  ~~ x + sumR xs    ...((foldrVectHomomorphism {f = plus} {e = 0}).cons x xs)
  <~ y + sumR ys    ...(plusLteMonotone  (prf 0) prf')
  ~~ sumR (y :: ys) ...(sym $ (foldrVectHomomorphism {f = plus} {e = 0}).cons y ys)
