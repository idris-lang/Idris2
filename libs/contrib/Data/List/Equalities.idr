module Data.List.Equalities

import Data.List

%default total

||| (::) is injective
export
consInjective : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
                (x :: xs) = (y :: ys) -> (x = y, xs = ys)
consInjective Refl = (Refl, Refl)

||| Two lists are equal, if their heads are equal and their tails are equal.
consCong2 : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
            x = y -> xs = ys -> x :: xs = y :: ys
consCong2 Refl Refl = Refl

||| Equal non-empty lists should result in equal componens after destructuring 'snoc'.
export
snocCong2 : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
            (xs `snoc` x) = (ys `snoc` y) -> (xs = ys, x = y)

snocCong2 {xs = []} {ys = []} Refl = (Refl, Refl)
snocCong2 {xs = []} {ys = z :: ys} prf = snocCong2 prf
snocCong2 {xs = w :: xs} {ys = []} prf = snocCong2 prf
snocCong2 {xs = w :: xs} {ys = z :: ys} prf =
  let (wEqualsZ, xsSnocXEqualsYsSnocY) = consInjective prf
      (xsEqualsYS, xEqualsY) = snocCong2 xsSnocXEqualsYsSnocY
   in (consCong2 wEqualsZ xsEqualsYS, xEqualsY)

 ||| Appending pairwise equal lists gives equal lists
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
mapAppendDistributive : (f : a -> b) -> (xs : List a) -> (ys : List a) ->
                        map f (xs ++ ys) = map f xs ++ map f ys
mapAppendDistributive _ [] _ = Refl
mapAppendDistributive f (x :: xs) ys =
  cong (f x ::) $ mapAppendDistributive f xs ys

||| List.length is distributive over appending.
export
lengthDistributive : (xs, ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthDistributive [] ys = Refl
lengthDistributive (x :: xs) ys = cong S $ lengthDistributive xs ys

export
lengthSnoc : (x : _) -> (xs : List a) -> length (snoc xs x) = S (length xs)
lengthSnoc x [] = Refl
lengthSnoc x (_ :: xs) = cong S (lengthSnoc x xs)
