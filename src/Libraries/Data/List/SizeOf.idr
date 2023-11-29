module Libraries.Data.List.SizeOf

import Data.List
import Libraries.Data.List.HasLength

%default total

public export
record SizeOf {a : Type} (xs : List a) where
  constructor MkSizeOf
  size        : Nat
  0 hasLength : HasLength size xs

export
0 theList : SizeOf {a} xs -> List a
theList _ = xs

public export
zero : SizeOf []
zero = MkSizeOf Z Z

public export
suc : SizeOf as -> SizeOf (a :: as)
suc (MkSizeOf n p) = MkSizeOf (S n) (S p)

-- ||| suc but from the right
export
sucR : SizeOf as -> SizeOf (as ++ [a])
sucR (MkSizeOf n p) = MkSizeOf (S n) (sucR p)

export
(+) : SizeOf xs -> SizeOf ys -> SizeOf (xs ++ ys)
MkSizeOf m p + MkSizeOf n q = MkSizeOf (m + n) (hlAppend p q)

export
mkSizeOf : (xs : List a) -> SizeOf xs
mkSizeOf xs = MkSizeOf (length xs) (mkHasLength xs)

export
reverse : SizeOf xs -> SizeOf (reverse xs)
reverse (MkSizeOf n p) = MkSizeOf n (hlReverse p)

export
map : SizeOf xs -> SizeOf (map f xs)
map (MkSizeOf n p) = MkSizeOf n (cast (sym $ lengthMap xs) p)

export
take : {n : Nat} -> {0 xs : Stream a} -> SizeOf (take n xs)
take = MkSizeOf n (take n xs)

namespace SizedView

  public export
  data SizedView : SizeOf as -> Type where
    Z : SizedView (MkSizeOf Z Z)
    S : (n : SizeOf as) -> SizedView (suc {a} n)

export
sizedView : (p : SizeOf as) -> SizedView p
sizedView (MkSizeOf Z Z)         = Z
sizedView (MkSizeOf (S n) (S p)) = S (MkSizeOf n p)
