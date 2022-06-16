||| This module contains stuff that may use functions from `Data.List`.
||| This separation is needed because `Data.List` uses `List1` type inside it,
||| thus the core of `List1` must not import `Data.List`.
module Data.List1.Properties

import Control.Function

import public Data.Maybe
import Data.List
import Data.List1

%default total

export
-- %deprecate -- deprecated in favor of Biinjective interface
consInjective : (x ::: xs) === (y ::: ys) -> (x === y, xs === ys)
consInjective Refl = (Refl, Refl)

export
Biinjective (:::) where
  biinjective Refl = (Refl, Refl)

export
{x : a} -> Injective (x :::) where
  injective Refl = Refl

export
{ys : List a} -> Injective (::: ys) where
  injective Refl = Refl

||| Proof that the length of a List1 is the same as the length
||| of the List it represents.
export
listLength : (xs : List1 a) -> length xs = length (forget xs)
listLength (head ::: tail) = Refl

------------------------------------------------------------------------
-- Properties of append involving usual `List`'s append

export
appendlNilRightNeutral : (l : List1 a) -> l `appendl` [] = l
appendlNilRightNeutral (_:::xs) = rewrite appendNilRightNeutral xs in Refl

export
lappendNilLeftNeutral : (l : List1 a) -> [] `lappend` l = l
lappendNilLeftNeutral l = Refl

export
appendAssociative : (l, c, r : List1 a) -> l ++ (c ++ r) = (l ++ c) ++ r
appendAssociative (l:::ls) (c:::cs) (r:::rs) = rewrite appendAssociative ls (c::cs) (r::rs) in Refl

export
toListAppendl : (xs : List1 a) -> (ys : List a) -> toList (xs `appendl` ys) = forget xs ++ ys
toListAppendl (x:::xs) ys = Refl

export
toListLappend : (xs : List a) -> (ys : List1 a) -> toList (xs `lappend` ys) = xs ++ forget ys
toListLappend []      ys = Refl
toListLappend (x::xs) ys = Refl

export
toListAppend : (xs, ys : List1 a) -> toList (xs ++ ys) = toList xs ++ toList ys
toListAppend (x:::xs) (y:::ys) = Refl

export
fromListAppend : (xs, ys : List a) -> fromList (xs ++ ys) = (fromList xs <+> fromList ys) @{Deep}
fromListAppend [] ys with (fromList ys)
  _ | Nothing  = Refl
  _ | (Just _) = Refl
fromListAppend (x::xs) ys with (fromList ys) proof prf
  fromListAppend (x::xs) []      | Nothing         = rewrite appendNilRightNeutral xs in Refl
  fromListAppend (x::xs) (y::ys) | (Just $ l:::ls) =
    let (Refl, Refl) = biinjective $ injective prf in Refl
