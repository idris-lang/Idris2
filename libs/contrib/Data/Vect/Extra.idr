||| Additional functions about vectors
module Data.Vect.Extra

import Data.Vect
import Data.Fin
import Data.Vect.Elem

||| Version of `map` with access to the current position
public export
mapI : (f : Fin len -> a -> b) -> Vect len a -> Vect len b
mapI f [] = []
mapI f (x :: xs) = f 0 x :: mapI (f . FS) xs

||| Version of `mapMaybe` with access to the current position
public export
mapMaybeI : (f : Fin len -> a -> Maybe b) -> Vect len a -> (m : Nat ** Vect m b)
mapMaybeI f []      = (_ ** [])
mapMaybeI f (x :: xs) =
  let (len ** ys) = mapMaybeI (f . FS) xs
    in case f FZ x of
       Just y  => (S len ** y :: ys)
       Nothing => (  len **      ys)

||| Version of `filter` with access to the current position
public export
filterI : (f : Fin len -> elem -> Bool) -> Vect len elem -> (m : Nat ** Vect m elem)
filterI p []      = ( _ ** [] )
filterI p (x :: xs) =
  let (_ ** tail) = filterI (p . FS) xs
   in if p FZ x then
        (_ ** x :: tail)
      else
        (_ ** tail)

||| Version of `foldl` with access to the current position
public export
foldlI : (f : acc -> Fin len -> elem -> acc) -> acc -> Vect len elem -> acc
foldlI f z [] = z
foldlI f z (x :: xs) = foldlI (flip (flip f . FS)) (f z 0 x) xs

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
