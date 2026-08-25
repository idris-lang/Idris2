module Libraries.Data.SnocList.HasLength

import Data.Nat

import Data.List.HasLength

import Data.SnocList

-- @TODO remove namespace disambiguation once prelude is updated.

namespace SnocList
  public export
  data HasLength : Nat -> SnocList a -> Type where
    Z : HasLength Z [<]
    S : HasLength n sa -> HasLength (S n) (sa :< a)

export
hasLength : SnocList.HasLength n sx -> length sx === n
hasLength Z = Refl
hasLength (S p) = cong S (hasLength p)

export
sucR : HasLength n sx -> HasLength (S n) (sx ++ [<x])
sucR = S

export
sucL : HasLength n sx -> HasLength (S n) ([<x] ++ sx)
sucL Z     = S Z
sucL (S n) = S (sucL n)

export
hlAppend : SnocList.HasLength m sx -> HasLength n sy -> HasLength (n + m) (sx ++ sy)
hlAppend sx Z = sx
hlAppend sx (S sy) = S (hlAppend sx sy)

export
hlFish : HasLength m sx -> List.HasLength.HasLength n ys -> HasLength (n + m) (sx <>< ys)
hlFish x Z = x
hlFish {n = S n} x (S y) = rewrite plusSuccRightSucc n m in hlFish (S x) y

export
mkHasLength : (sx : SnocList a) -> HasLength (length sx) sx
mkHasLength [<] = Z
mkHasLength (sx :< _) = S (mkHasLength sx)

export
hlChips : HasLength m sx -> List.HasLength.HasLength n ys -> List.HasLength.HasLength (m + n) (sx <>> ys)
hlChips Z y = y
hlChips {m = S m} {n} (S x) y
  = rewrite plusSuccRightSucc m n in
    hlChips x (S y)

{-
export
take : (n : Nat) -> (xs : Stream a) -> HasLength n (take n xs)
take Z _ = Z
take (S n) (x :: xs) = S (take n xs)
-}

export
cast : {sy : _} -> (0 _ : SnocList.length sx = SnocList.length sy) ->
       SnocList.HasLength m sx -> SnocList.HasLength m sy
cast {sy = [<]} eq Z = Z
cast {sy = sy :< _} eq (S p) = S (cast (injective eq) p)

hlReverseOnto : SnocList.HasLength m acc -> HasLength n sx -> HasLength (m + n) (reverseOnto acc sx)
hlReverseOnto p Z = rewrite plusZeroRightNeutral m in p
hlReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hlReverseOnto (S p) q

export
hlReverse : SnocList.HasLength m acc -> HasLength m (reverse acc)
hlReverse = hlReverseOnto Z
