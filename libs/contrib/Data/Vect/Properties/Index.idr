||| Properties of Data.Vect.index
module Data.Vect.Properties.Index

import Data.Vect.Properties.Tabulate

import Data.Vect
import Data.Vect.Elem
import Data.Fin

import Syntax.PreorderReasoning

||| Recall an element by its position, as we may not have the element
||| at runtime
public export
recallElem : {xs : Vect n a} -> x `Elem` xs -> a
recallElem {xs = x :: _ }  Here         = x
recallElem {xs = _ :: xs} (There later) = recallElem later

||| Recalling by a position of `x` does yield `x`
export
recallElemSpec : (pos : x `Elem` xs) -> recallElem pos = x
recallElemSpec  Here         = Refl
recallElemSpec (There later) = recallElemSpec later

||| `index i : Vect n a -> a` is a natural transformation
export
indexNaturality : (i : Fin n) -> (f : a -> b) -> (xs : Vect n a)
  -> index i (map f xs) = f (index i xs)
indexNaturality  FZ    f (x :: xs) = Refl
indexNaturality (FS x) f (_ :: xs)  = indexNaturality x f xs

||| Replication tabulates the constant function
export
indexReplicate : (i : Fin n) -> (x : a)
  -> index i (replicate n x) = x
indexReplicate  FZ    x = Refl
indexReplicate (FS i) x = indexReplicate i x

||| `range` tabulates the identity function (by definition)
export
indexRange : (i : Fin n) -> index i (range {len = n}) === i
indexRange i = irrelevantEq $ indexTabulate id i

||| Inductive step auxiliary lemma for indexTranspose
indexZipWith_Cons : (i : Fin n) -> (xs : Vect n a) -> (xss : Vect n (Vect m a))
  -> index i (zipWith (::) xs xss)
  = (index i xs)       :: (index i xss)
indexZipWith_Cons  FZ    (x :: _ ) (xs:: _  ) = Refl
indexZipWith_Cons (FS i) (_ :: xs) (_ :: xss) = indexZipWith_Cons i xs xss

||| The `i`-th vector in a transposed matrix is the vector of `i`-th components
export
indexTranspose : (xss : Vect m (Vect n a)) -> (i : Fin n)
  -> index i (transpose xss) = map (index i) xss
indexTranspose     []      i = indexReplicate i []
indexTranspose (xs :: xss) i = Calc $
  |~ index i (transpose (xs :: xss))
  ~~ index i (zipWith (::) xs (transpose xss))  ...(Refl)
  ~~ index i xs :: index i (transpose xss)      ...(indexZipWith_Cons i xs (transpose xss))
  ~~ index i xs :: map (index i) xss            ...(cong (index i xs ::)
                                                         $ indexTranspose xss i)
