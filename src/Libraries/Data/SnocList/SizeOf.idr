module Libraries.Data.SnocList.SizeOf

import Data.List
import Data.SnocList
import Data.List.HasLength
import Libraries.Data.SnocList.HasLength

---------------------------------------
-- horrible hack
import Libraries.Data.List.SizeOf as L

public export
0 LSizeOf : {0 a : Type} -> List a -> Type
LSizeOf xs = L.SizeOf xs

%hide L.SizeOf
---------------------------------------

%default total

public export
record SizeOf {a : Type} (sx : SnocList a) where
  constructor MkSizeOf
  size        : Nat
  0 hasLength : HasLength size sx

export
0 theList : SizeOf {a} sx -> SnocList a
theList _ = sx

public export
Lin : SizeOf [<]
Lin = MkSizeOf Z Z

public export
(:<) : SizeOf as -> (0 a : _) -> SizeOf (as :< a)
MkSizeOf n p :< _ = MkSizeOf (S n) (S p)

public export
zero : SizeOf [<]
zero = MkSizeOf Z Z

public export
suc : SizeOf as -> SizeOf (as :< a)
suc (MkSizeOf n p) = MkSizeOf (S n) (S p)

-- ||| suc but from the left
export
sucL : SizeOf as -> SizeOf ([<a] ++ as)
sucL (MkSizeOf n p) = MkSizeOf (S n) (sucL p)

public export
(<><) : SizeOf {a} sx -> LSizeOf {a} ys -> SizeOf (sx <>< ys)
MkSizeOf m p <>< MkSizeOf n q = MkSizeOf (n + m) (hlFish p q)

public export
(<>>) : SizeOf {a} sx -> LSizeOf {a} ys -> LSizeOf (sx <>> ys)
MkSizeOf m p <>> MkSizeOf n q = MkSizeOf (m + n) (hlChips p q)

export
cast : LSizeOf {a} xs -> SizeOf {a} (cast xs)
cast = ([<] <><)

export
(+) : SizeOf sx -> SizeOf sy -> SizeOf (sx ++ sy)
MkSizeOf m p + MkSizeOf n q = MkSizeOf (n + m) (hlAppend p q)

export
mkSizeOf : (sx : SnocList a) -> SizeOf sx
mkSizeOf sx = MkSizeOf (length sx) (mkHasLength sx)

export
reverse : SizeOf sx -> SizeOf (reverse sx)
reverse (MkSizeOf n p) = MkSizeOf n (hlReverse p)

export
map : SizeOf sx -> SizeOf (map f sx)
map (MkSizeOf n p) = MkSizeOf n (cast (sym $ lengthMap sx) p) where

  lengthMap : (sx : _) -> SnocList.length (map f sx) === SnocList.length sx
  lengthMap [<] = Refl
  lengthMap (sx :< x) = cong S (lengthMap sx)

{-
export
take : {n : Nat} -> {0 sx : Stream a} -> SizeOf (take n sx)
take = MkSizeOf n (take n sx)
-}

namespace SizedView

  public export
  data SizedView : SizeOf as -> Type where
    Z : SizedView [<]
    S : (n : SizeOf as) -> SizedView (n :< a)

export
sizedView : (p : SizeOf as) -> SizedView p
sizedView (MkSizeOf Z Z)         = Z
sizedView (MkSizeOf (S n) (S p)) = S (MkSizeOf n p)
