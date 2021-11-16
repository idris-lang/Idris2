module Data.List.Views

import Control.Relation
import Control.WellFounded
import Data.List
import Data.Nat

%default total

lengthSuc : (xs : List a) -> (y : a) -> (ys : List a) ->
            length (xs ++ (y :: ys)) = S (length (xs ++ ys))
lengthSuc [] _ _ = Refl
lengthSuc (x :: xs) y ys = cong S (lengthSuc xs y ys)

lengthLT : (xs : List a) -> (ys : List a) ->
           LTE (length xs) (length (ys ++ xs))
lengthLT xs [] = reflexive {x = length xs}
lengthLT xs (x :: ys) = lteSuccRight (lengthLT _ _)

smallerLeft : (ys : List a) -> (y : a) -> (zs : List a) ->
              LTE (S (S (length ys))) (S (length (ys ++ (y :: zs))))
smallerLeft [] y zs = LTESucc (LTESucc LTEZero)
smallerLeft (z :: ys) y zs = LTESucc (smallerLeft ys _ _)

smallerRight : (ys : List a) -> (zs : List a) ->
               LTE (S (S (length zs))) (S (length (ys ++ (y :: zs))))
smallerRight ys zs = rewrite lengthSuc ys y zs in
                     (LTESucc (LTESucc (lengthLT _ _)))

||| View for splitting a list in half, non-recursively
public export
data Split : List a -> Type where
     SplitNil : Split []
     SplitOne : (x : a) -> Split [x]
     SplitPair : (x : a) -> (xs : List a) ->
                 (y : a) -> (ys : List a) ->
                 Split (x :: xs ++ y :: ys)

splitHelp : (head : a) ->
            (xs : List a) ->
            (counter : List a) -> Split (head :: xs)
splitHelp head [] counter = SplitOne _
splitHelp head (x :: xs) [] = SplitPair head [] x xs
splitHelp head (x :: xs) [y] = SplitPair head [] x xs
splitHelp head (x :: xs) (_ :: _ :: ys)
    = case splitHelp head xs ys of
           SplitOne x => SplitPair x [] _ []
           SplitPair x' xs y' ys => SplitPair x' (x :: xs) y' ys

||| Covering function for the `Split` view
||| Constructs the view in linear time
export
split : (xs : List a) -> Split xs
split [] = SplitNil
split (x :: xs) = splitHelp x xs xs

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
    splitRec (y :: ys ++ z :: zs) | Access acc | SplitPair y ys z zs
      = SplitRecPair _ _
          (splitRec (y :: ys) | acc _ (smallerLeft ys z zs))
          (splitRec (z :: zs) | acc _ (smallerRight ys zs))

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
