||| This module contains stuff that may use functions from `Data.List`.
||| This separation is needed because `Data.List` uses `List1` type inside it,
||| thus the core of `List1` must not import `Data.List`.
module Data.List1.Properties

import Control.Function

import public Data.Maybe
import Data.List
import Data.List1

%default total

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
  fromListAppend (x::xs) (y::ys) | (Just $ l:::ls) = do
    let (prfL, prfLs) = consInjective $ injective prf
    rewrite prfL; rewrite prfLs; Refl
