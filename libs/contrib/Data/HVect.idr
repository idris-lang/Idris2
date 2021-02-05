module Data.HVect

import Decidable.Equality
import Data.List
import public Data.Vect
import Data.Vect.Elem

%default total

||| Heterogeneous vectors where the type index gives, element-wise,
||| the types of the contents.
public export
data HVect : Vect k Type -> Type where
  Nil : HVect []
  (::) : t -> HVect ts -> HVect (t :: ts)

||| Extract an element from an HVect.
|||
||| ```idris example
||| > index 0 (the (HVect _) [1, "string"])
||| 1
||| ```
public export
index : (i : Fin k) -> HVect ts -> index i ts
index FZ (x :: xs) = x
index (FS j) (x :: xs) = index j xs

||| Delete an element from an HVect.
|||
||| ```idris example
||| > deleteAt 0 (the (HVect _) [1, "string"])
||| ["string"]
||| ```
public export
deleteAt : (i : Fin (S l)) -> HVect ts -> HVect (deleteAt i ts)
deleteAt FZ (x :: xs) = xs
deleteAt (FS FZ) (x :: (y :: xs)) = x :: xs
deleteAt (FS (FS j)) (x :: (y :: xs)) = x :: deleteAt (FS j) (y :: xs)

||| Replace an element in an HVect.
|||
||| ```idris example
||| > replaceAt 0 "firstString" (the (HVect _) [1, "string"])
||| ["firstString", "string"]
||| ```
public export
replaceAt : (i : Fin k) -> t -> HVect ts -> HVect (replaceAt i t ts)
replaceAt FZ y (x :: xs) = y :: xs
replaceAt (FS j) y (x :: xs) = x :: replaceAt j y xs

||| Update an element in an HVect.
|||
||| ```idris example
||| > updateAt 0 (const True) (the (HVect _) [1, "string"])
||| [True, "string"]
||| ```
public export
updateAt : (i : Fin k) -> (index i ts -> t) -> HVect ts -> HVect (replaceAt i t ts)
updateAt FZ f (x :: xs) = f x :: xs
updateAt (FS j) f (x :: xs) = x :: updateAt j f xs

||| Append two `HVect`s.
|||
||| ```idris example
||| > (the (HVect _) [1]) ++ (the (HVect _) ["string"])
||| [1, "string"]
||| ```
public export
(++) : HVect ts -> HVect us -> HVect (ts ++ us)
(++) [] ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

public export
Eq (HVect []) where
  [] == [] = True

public export
(Eq t, Eq (HVect ts)) => Eq (HVect (t :: ts)) where
  (x :: xs) == (y :: ys) = x == y && xs == ys

public export
consInjective1 : {0 xs, ys: HVect ts} -> {0 x, y: a} -> (x :: xs = y :: ys) -> x = y
consInjective1 Refl = Refl

public export
consInjective2 : {0 xs, ys: HVect ts} -> {0 x, y: a} -> (x :: xs = y :: ys) -> xs = ys
consInjective2 Refl = Refl

public export
DecEq (HVect []) where
  decEq [] [] = Yes Refl

public export
(DecEq t, DecEq (HVect ts)) => DecEq (HVect (t :: ts)) where
  decEq (x :: xs) (y :: ys) with (decEq x y)
    decEq (z :: xs) (z :: ys) | Yes Refl with (decEq xs ys)
      decEq (z :: zs) (z :: zs) | Yes Refl | Yes Refl = Yes Refl
      decEq (z :: xs) (z :: ys) | Yes Refl | No contra = No (contra . consInjective2)
    decEq (x :: xs) (y :: ys) | No contra = No (contra . consInjective1)

public export
interface Shows k ts where
  shows : HVect {k} ts -> Vect k String

public export
Shows Z [] where
  shows [] = []

public export
(Show t, Shows len ts) => Shows (S len) (t :: ts) where
  shows (x :: xs) = show x :: shows xs

public export
(Shows len ts) => Show (HVect ts) where
  show xs = "[" ++ (pack . intercalate [','] . map unpack . toList $ shows xs) ++ "]"

||| Extract an arbitrary element of the correct type.
|||
||| ```idris example
||| > get [1, "string"] {p = Here}
||| 1
||| ```
public export
get : (1 _ : HVect ts) -> {auto 1 p : Elem t ts} -> t
get (x :: xs) {p = Here} = x
get (x :: xs) {p = (There p')} = get xs

||| Replace an element with the correct type. (Homogeneous)
|||
||| ```idris example
||| > put 2 [1, "string"]
||| [2, "string"]
||| ```
public export
put : t -> (1 _ : HVect ts) -> {auto 1 p : Elem t ts} -> HVect ts
put y (x :: xs) {p = Here} = y :: xs
put y (x :: xs) {p = (There p')} = x :: put y xs

||| Replace an element with the correct type. (Heterogeneous)
|||
||| ```idris example
||| > htPut True [1, "string"] {p = Here}
||| [True, "string"]
||| ```
public export
htPut : u -> (1 _ : HVect ts) -> {auto 1 p : Elem t ts} -> HVect (replaceByElem ts p u)
htPut y (x :: xs) {p = Here} = y :: xs
htPut y (x :: xs) {p = There p'} = x :: htPut y xs

||| Update an element with the correct type. (Homogeneous)
|||
||| ```idris example
||| > update (const "hello world!") [1, "string"]
||| [1, "hello world!"]
||| ```
public export
update : (t -> t) -> (1 _ : HVect ts) -> {auto 1 p : Elem t ts} -> HVect ts
update f (x :: xs) {p = Here} = f x :: xs
update f (x :: xs) {p = There p'} = x :: update f xs

||| Update an element with the correct type. (Heterogeneous)
|||
||| ```idris example
||| > htUpdate (\_ : String => 2) [1, "string"]
||| [1, 2]
||| ```
public export
htUpdate : (t -> u) -> (1 _ : HVect ts) -> {auto 1 p : Elem t ts} -> HVect (replaceByElem ts p u)
htUpdate f (x :: xs) {p = Here} = f x :: xs
htUpdate f (x :: xs) {p = (There p')} = x :: htUpdate f xs
