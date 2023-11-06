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
