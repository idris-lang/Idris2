module Libraries.Data.List.HasLength

import Data.Nat

-- TODO: delete in favor of base lib's List.HasLength once next version _after_ v0.6.0 ships.
public export
data HasLength : Nat -> List a -> Type where
  Z : HasLength Z []
  S : HasLength n as -> HasLength (S n) (a :: as)

-- TODO: Use List.HasLength.sucR from the base lib instead once next version _after_ v0.6.0 ships.
export
sucR : HasLength n xs -> HasLength (S n) (xs ++ [x])
sucR Z     = S Z
sucR (S n) = S (sucR n)

-- TODO: Use List.HasLength.hasLengthAppend from the base lib instead once next version _after_ v0.6.0 ships.
export
hlAppend : HasLength m xs -> HasLength n ys -> HasLength (m + n) (xs ++ ys)
hlAppend Z ys = ys
hlAppend (S xs) ys = S (hlAppend xs ys)

-- TODO: Use List.HasLength.hasLength from the base lib instead once next version _after_ v0.6.0 ships.
export
mkHasLength : (xs : List a) -> HasLength (length xs) xs
mkHasLength [] = Z
mkHasLength (_ :: xs) = S (mkHasLength xs)

-- TODO: Use List.HasLength.take from the base lib instead once next vresion _after_ v0.6.0 ships.
export
take : (n : Nat) -> (xs : Stream a) -> HasLength n (take n xs)
take Z _ = Z
take (S n) (x :: xs) = S (take n xs)

export
cast : {ys : _} -> (0 _ : List.length xs = List.length ys) -> HasLength m xs -> HasLength m ys
cast {ys = []}      eq Z = Z
cast {ys = y :: ys} eq (S p) = S (cast (injective eq) p)

-- TODO: Delete once version _after_ v0.6.0 ships.
hlReverseOnto : HasLength m acc -> HasLength n xs -> HasLength (m + n) (reverseOnto acc xs)
hlReverseOnto p Z = rewrite plusZeroRightNeutral m in p
hlReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hlReverseOnto (S p) q

-- TODO: Use List.HasLength.hasLengthReverse from the base lib instead once next version _after_ v0.6.0 ships.
export
hlReverse : HasLength m acc -> HasLength m (reverse acc)
hlReverse = hlReverseOnto Z
