||| Tabulation gives a bijection between functions `f : Fin n -> a`
||| (up to extensional equality) and vectors `tabulate f : Vect n a`.
module Data.Vect.Properties.Tabulate

import Data.Vect
import Data.Fin

||| Vectors are uniquely determined by their elements
export
vectorExtensionality
  : (xs, ys : Vect n a) -> (ext : (i : Fin n) -> index i xs = index i ys)
 -> xs = ys
vectorExtensionality    []        []     ext = Refl
vectorExtensionality (x :: xs) (y :: ys) ext =
  cong2 (::)
        (ext FZ)
        (vectorExtensionality xs ys (\i => ext (FS i)))

||| Extensionally equivalent functions tabulate to the same vector
export
tabulateExtensional
  : {n : Nat} -> (f, g : Fin n -> a) -> (ext : (i : Fin n) -> f i = g i)
 -> tabulate f = tabulate g
tabulateExtensional {n = 0  } f g ext = Refl
tabulateExtensional {n = S n} f g ext =
  cong2 (::) (ext FZ) (tabulateExtensional (f . FS) (g . FS) (\ i => ext $ FS i))

||| Taking an index amounts to applying the tabulated function
export
indexTabulate : {n : Nat} -> (f : Fin n -> a) -> (i : Fin n) -> index i (tabulate f) = f i
indexTabulate f  FZ    = Refl
indexTabulate f (FS i) = indexTabulate (f . FS) i

||| The empty vector represents the unique function `Fin 0 -> a`
export
emptyInitial : (v : Vect 0 a) -> v = []
emptyInitial [] = Refl
