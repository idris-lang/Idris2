module Data.List.Views

import Control.Relation
import Control.WellFounded
import Data.List
import Data.Nat
import Data.Nat.Views

%default total

lengthSum : (xs, ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthSum [] ys = Refl
lengthSum (x::xs) ys
  = rewrite consAppend x xs ys in
      rewrite lengthSum xs ys in
        Refl

smallerLeft : (y : a) -> (ys : List a) -> (z : a) -> (zs : List a) ->
              LTE (S (S (length ys))) (length ((y :: ys) ++ (z :: zs)))
smallerLeft y ys z zs
  = rewrite lengthSum (y :: ys) (z :: zs) in
      rewrite sym $ plusSuccRightSucc (length ys) (length zs) in
        LTESucc $ LTESucc $ lteAddRight (length ys)

lteAddLeft : (n : Nat) -> LTE n (m + n)
lteAddLeft {m} n = rewrite plusCommutative m n in lteAddRight n

smallerRight : (y : a) -> (ys : List a) -> (z : a) -> (zs : List a) ->
               LTE (S (S (length zs))) (length ((y :: ys) ++ (z :: zs)))
smallerRight y ys z zs
  = rewrite lengthSum (y :: ys) (z :: zs) in
      LTESucc $ lteAddLeft (S (length zs))

||| View for splitting a list in half, non-recursively
public export
data Split : List a -> Type where
     SplitNil : Split []
     SplitOne : (x : a) -> Split [x]
     ||| If output by the `split` function, (x::xs) will have length equal to
     ||| or one plus the length of (y::ys)
     SplitPair : (x : a) -> (xs : List a) ->
                 (y : a) -> (ys : List a) ->
                 Split ((x :: xs) ++ (y :: ys))

splitHelp : (x : a) ->
            (xs : List a) ->
            (y : a) ->
            (ys : List a) ->
            (counter : List a) ->
            Split (x :: (reverse xs ++ (y::ys)))
splitHelp x xs y [] _
  = rewrite sym $ consAppend x (reverse xs) [y] in
      SplitPair x (reverse xs) y []
splitHelp x xs y ys []
  = rewrite sym $ consAppend x (reverse xs) (y::ys) in
      SplitPair x (reverse xs) y ys
splitHelp x xs y0 (y1::ys) (c::cs)
  = rewrite reverseInvolutive xs in
      rewrite cong (\u => reverseOnto (y1::ys) u) $ sym $ reverseInvolutive (y0::xs) in
        splitHelp x (y0::xs) y1 ys (drop 1 cs)

||| Covering function for the `Split` view
||| Constructs the view in linear time
export
split : (xs : List a) -> Split xs
split [] = SplitNil
split [x] = SplitOne x
split (x0::x1::xs) = splitHelp x0 [] x1 xs xs

public export
data SplitRec : List a -> Type where
     SplitRecNil : SplitRec []
     SplitRecOne : (x : a) -> SplitRec [x]
     SplitRecPair : (lefts, rights : List a) -> -- Explicit, don't erase
                    (lrec : Lazy (SplitRec lefts)) ->
                    (rrec : Lazy (SplitRec rights)) -> SplitRec (lefts ++ rights)

||| Covering function for the `SplitRec` view
||| Constructs the view in O(n lg n)
public export
splitRec : (xs : List a) -> SplitRec xs
splitRec xs with (sizeAccessible xs)
  splitRec xs | acc with (split xs)
    splitRec []  | acc | SplitNil = SplitRecNil
    splitRec [x] | acc | SplitOne x = SplitRecOne x
    splitRec ((y :: ys) ++ (z :: zs)) | Access acc | SplitPair y ys z zs
      = SplitRecPair _ _
          (splitRec (y :: ys) | acc _ (smallerLeft y ys z zs))
          (splitRec (z :: zs) | acc _ (smallerRight y ys z zs))

||| View for traversing a list backwards
public export
data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (x : a) -> (xs : List a) ->
            (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : {input : _} ->
               SnocList input -> (rest : List a) -> SnocList (input ++ rest)
snocListHelp snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp snoc (x :: xs)
   = rewrite appendAssociative input [x] xs in
             snocListHelp (Snoc x input snoc) xs

||| Covering function for the `SnocList` view
||| Constructs the view in linear time
export
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs
