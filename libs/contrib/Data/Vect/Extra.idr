||| Additional functions about vectors
module Data.Vect.Extra

import Data.Vect
import Data.Fin
import Data.Vect.Elem

||| Enumerate a Vect with indicies of Fin
public export
enumFin : Vect n a -> Vect n (Fin n, a)
enumFin [] = []
enumFin (x :: xs) = (FZ, x) :: map (\(n, s) => (FS n, s)) (enumFin xs)

||| Enumerate a Vect with indicies of Elem
public export
enumElem : (l : Vect n a) -> Vect n (e : a ** Elem e l)
enumElem [] = []
enumElem (x :: xs) = (x ** Here) :: map (\(s ** f) => (s ** There f)) (enumElem xs)

||| Version of `map` with runtime-irrelevant information that the
||| argument is an element of the vector
public export
mapWithElem : (xs : Vect n a)
  -> (f : (x : a) -> (0 pos : x `Elem` xs) -> b)
  -> Vect n b
mapWithElem []        f = []
mapWithElem (x :: xs) f
  = f x Here :: mapWithElem xs
                (\x,pos => f x (There pos))
