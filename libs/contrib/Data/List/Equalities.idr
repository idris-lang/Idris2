module Data.List.Equalities

import Data.List

%default total

||| A list constructued using snoc cannot be empty.
export
snocNonEmpty : {x : a} -> {xs : List a} -> xs ++ [x] = [] -> Void
snocNonEmpty {xs = []} prf = uninhabited prf
snocNonEmpty {xs = y :: ys} prf = uninhabited prf

||| (::) is injective
export
consInjective : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
                (x :: xs) = (y :: ys) -> (x = y, xs = ys)
consInjective Refl = (Refl, Refl)

||| Two lists are equal, if their heads are equal and their tails are equal.
export
consCong2 : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
            x = y -> xs = ys -> x :: xs = y :: ys
consCong2 Refl Refl = Refl

||| Equal non-empty lists should result in equal components after destructuring 'snoc'.
export
snocInjective : {x : a} -> {xs : List a} -> {y : a} -> {ys : List a} ->
            (xs `snoc` x) = (ys `snoc` y) -> (xs = ys, x = y)
snocInjective {xs = []} {ys = []} Refl = (Refl, Refl)
snocInjective {xs = []} {ys = z :: zs} prf =
  let nilIsSnoc = snd $ consInjective {xs = []} {ys = zs ++ [y]} prf
   in void $ snocNonEmpty (sym nilIsSnoc)
snocInjective {xs = z :: xs} {ys = []} prf =
  let snocIsNil = snd $ consInjective {x = z} {xs = xs ++ [x]} {ys = []} prf
   in void $ snocNonEmpty snocIsNil
snocInjective {xs = w :: xs} {ys = z :: ys} prf =
  let (wEqualsZ, xsSnocXEqualsYsSnocY) = consInjective prf
      (xsEqualsYS, xEqualsY) = snocInjective xsSnocXEqualsYsSnocY
   in (consCong2 wEqualsZ xsEqualsYS, xEqualsY)

||| Appending pairwise equal lists gives equal lists
export
appendCong2 : {x1 : List a} -> {x2 : List a} ->
              {y1 : List b} -> {y2 : List b} ->
              x1 = y1 -> x2 = y2 -> x1 ++ x2 = y1 ++ y2
appendCong2 {x1=[]} {y1=(_ :: _)} Refl _ impossible
appendCong2 {x1=(_ :: _)} {y1=[]} Refl _ impossible
appendCong2 {x1=[]} {y1=[]} _ eq2 = eq2
appendCong2 {x1=(_ :: _)} {y1=(_ :: _)} eq1 eq2 =
  let (hdEqual, tlEqual) = consInjective eq1
   in consCong2 hdEqual (appendCong2 tlEqual eq2)

||| List.map is distributive over appending.
export
mapDistributesOverAppend
  : (f : a -> b)
  -> (xs : List a)
  -> (ys : List a)
  -> map f (xs ++ ys) = map f xs ++ map f ys
mapDistributesOverAppend _ [] _ = Refl
mapDistributesOverAppend f (x :: xs) ys =
  cong (f x ::) $ mapDistributesOverAppend f xs ys

||| List.length is distributive over appending.
export
lengthDistributesOverAppend
  : (xs, ys : List a)
  -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys =
  cong S $ lengthDistributesOverAppend xs ys

||| Length of a snoc'd list is the same as Succ of length list.
export
lengthSnoc : (x : _) -> (xs : List a) -> length (snoc xs x) = S (length xs)
lengthSnoc x [] = Refl
lengthSnoc x (_ :: xs) = cong S (lengthSnoc x xs)
