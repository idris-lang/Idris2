module Libraries.Data.SnocList.HasLength

import Data.Nat

public export
data HasLength : Nat -> SnocList a -> Type where
  Z : HasLength Z [<]
  S : HasLength n sa -> HasLength (S n) (sa :< a)

export
sucL : HasLength n sx -> HasLength (S n) ([<x] ++ sx)
sucL Z     = S Z
sucL (S n) = S (sucL n)

export
hlAppend : HasLength m sx -> HasLength n sy -> HasLength (n + m) (sx ++ sy)
hlAppend sx Z = sx
hlAppend sx (S sy) = S (hlAppend sx sy)

export
mkHasLength : (sx : SnocList a) -> HasLength (length sx) sx
mkHasLength [<] = Z
mkHasLength (sx :< _) = S (mkHasLength sx)

{-
export
take : (n : Nat) -> (sx : Stream a) -> HasLength n (take n sx)
take Z _ = Z
take (S n) (x :: sx) = S (take n sx)
-}

export
cast : {sy : _} -> (0 _ : SnocList.length sx = SnocList.length sy) ->
       HasLength m sx -> HasLength m sy
cast {sy = [<]} eq Z = Z
cast {sy = sy :< _} eq (S p) = S (cast (injective eq) p)

hlReverseOnto : HasLength m acc -> HasLength n sx -> HasLength (m + n) (reverseOnto acc sx)
hlReverseOnto p Z = rewrite plusZeroRightNeutral m in p
hlReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hlReverseOnto (S p) q

export
hlReverse : HasLength m acc -> HasLength m (reverse acc)
hlReverse = hlReverseOnto Z
