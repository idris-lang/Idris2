module Libraries.Data.SnocList.Extra

import Data.SnocList

export
lengthDistributesOverAppend
  : (xs, ys : SnocList a)
  -> length (xs ++ ys) = length ys + length xs
lengthDistributesOverAppend xs [<] = Refl
lengthDistributesOverAppend xs (ys :< y) =
  cong S $ lengthDistributesOverAppend xs ys

export
snocAppendAsFish : (sx, sy : SnocList a) -> sx ++ sy === sx <>< (cast sy)
snocAppendAsFish sx sy = sym
  $ trans (fishAsSnocAppend sx (sy <>> []))
          (cong (sx ++) (castToList sy))

export
index' : SnocList a -> Nat -> Maybe a
index' (_ :< x) Z = Just x
index' (xs :< _) (S k) = index' xs k
index' [<] _ = Nothing

export
snocAppendFishAssociative :
  (sx, sy : SnocList a) -> (zs : List a) ->
  (sx ++ sy) <>< zs === sx ++ (sy <>< zs)
snocAppendFishAssociative sx sy [] = Refl
snocAppendFishAssociative sx sy (z :: zs)
  = snocAppendFishAssociative sx (sy :< z) zs

export
lookup : Eq a => a -> SnocList (a, b) -> Maybe b
lookup k [<] = Nothing
lookup k (xs :< (x, v))
  = ifThenElse (k == x) (Just v) (lookup k xs)
