module Data.Vect.Properties.Fin

import Data.Vect
import Data.Vect.Elem
import Data.Vect.Extra
import Data.Fin
import Data.Nat

||| Witnesses non-empty runtime-irrelevant vectors. Analogous to Data.List.NonEmpty
public export
data NonEmpty : Vect n a -> Type where
  IsNonEmpty : NonEmpty (x :: xs)

||| eta-law (extensionality) of head-tail cons
export
etaCons : (xs : Vect (S n) a) -> head xs :: tail xs = xs
etaCons (x :: xs) = Refl

||| Inhabitants of `Fin n` witness `NonZero n`
export
finNonZero : Fin n -> NonZero n
finNonZero  FZ    = SIsNonZero
finNonZero (FS i) = SIsNonZero

||| Inhabitants of `Fin n` witness runtime-irrelevant vectors of length `n` aren't empty
export
finNonEmpty : (0 xs : Vect n a) -> NonZero n -> NonEmpty xs
finNonEmpty xs SIsNonZero = replace {p = NonEmpty} (etaCons xs) IsNonEmpty

||| Cast an index into a runtime-irrelevant `Vect` into the position
||| of the corresponding element
public export
finToElem : (0 xs : Vect n a) -> (i : Fin n) -> (index i xs) `Elem` xs
finToElem  {n      }       xs  i with (finNonEmpty xs $ finNonZero i)
 finToElem {n = S n} (x :: xs)  FZ    | IsNonEmpty = Here
 finToElem {n = S n} (x :: xs) (FS i) | IsNonEmpty = There (finToElem xs i)

||| Analogus to `indexNaturality`, but morhisms can (irrelevantly) know the context
export
indexNaturalityWithElem : (i : Fin n) -> (xs : Vect n a) -> (f : (x : a) -> (0 pos : x `Elem` xs) -> b)
  -> index i (mapWithElem xs f) = f (index i xs) (finToElem xs i)
indexNaturalityWithElem  {n    } i       xs  f with (finNonEmpty xs (finNonZero i))
 indexNaturalityWithElem {n = _}  FZ    (x :: xs) f | IsNonEmpty = Refl
 indexNaturalityWithElem {n = _} (FS i) (x :: xs) f | IsNonEmpty = indexNaturalityWithElem i xs _
