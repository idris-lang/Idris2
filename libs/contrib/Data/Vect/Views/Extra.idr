||| Additional views for Vect
module Data.Vect.Views.Extra

import Control.WellFounded
import Data.Vect
import Data.Nat


||| View for splitting a vector in half, non-recursively
public export
data Split : Vect n a -> Type where
    SplitNil : Split []
    SplitOne : Split [x]
    ||| two non-empty parts
    SplitPair : {n : Nat} -> {m : Nat} ->
                {x, y : a} -> {xs : Vect n a} -> {ys : Vect m a} ->
                Split (x :: xs ++ y :: ys)

total
splitHelp : {n: Nat} -> (head : a) -> (zs : Vect n a) ->
            Nat -> Split (head :: zs)
splitHelp head [] _ = SplitOne
splitHelp head (z :: zs) 0 = SplitPair {xs = []} {ys = zs}
splitHelp head (z :: zs) 1 = SplitPair {xs = []} {ys = zs}
splitHelp head (z :: zs) (S (S k))
  = case splitHelp head zs k of
         SplitOne => SplitPair {xs = []} {ys = []}
         SplitPair {xs} {ys} => SplitPair {xs = z :: xs} {ys = ys}

||| Covering function for the `Split` view
||| Constructs the view in linear time
export total
split : {n: Nat} -> (xs : Vect n a) -> Split xs
split [] = SplitNil
split {n = S k} (x :: xs) = splitHelp x xs k

||| View for splitting a vector in half, recursively
|||
||| This allows us to define recursive functions which repeatedly split vectors
||| in half, with base cases for the empty and singleton lists.
public export
data SplitRec : Vect k a -> Type where
  SplitRecNil : SplitRec []
  SplitRecOne : SplitRec [x]
  SplitRecPair : {n : Nat} -> {m : Nat} -> {xs : Vect (S n) a} -> {ys : Vect (S m) a} ->
    (lrec  : Lazy (SplitRec xs)) -> (rrec : Lazy (SplitRec ys)) -> SplitRec (xs ++ ys)

smallerPlusL : (m: Nat) -> (k: Nat) -> LTE (S (S m)) (S (m + (S k)))
smallerPlusL m k = rewrite sym (plusSuccRightSucc m k) in (LTESucc (LTESucc (lteAddRight _)))

smallerPlusR : (m: Nat) -> (k: Nat) -> LTE (S (S k)) (S (plus m (S k)))
smallerPlusR m k = rewrite sym (plusSuccRightSucc m k) in
                    LTESucc (LTESucc (rewrite plusCommutative m k in (lteAddRight _)))

||| Covering function for the `SplitRec` view
||| Constructs the view in O(n lg n)
public export total
splitRec : {k : Nat} -> (xs : Vect k a) -> SplitRec xs
splitRec {k} input with (sizeAccessible k)
  splitRec {k} input | acc with (split input)
    splitRec {k = 0} [] | acc | SplitNil = SplitRecNil
    splitRec {k = 1} [x] | acc | SplitOne = SplitRecOne
    splitRec {k = (S nl + S nr)} (x :: xs ++ y :: ys) | Access rec | SplitPair {x} {xs} {y} {ys} =
      SplitRecPair
        (splitRec {k = (S nl)} (x :: xs) | rec _ (smallerPlusL nl nr))
        (splitRec {k = (S nr)} (y :: ys) | rec _ (smallerPlusR nl nr))
