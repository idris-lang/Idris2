module Core.Name.ScopedList.SizeOf

import Data.Nat

import Libraries.Data.SnocList.SizeOf

import Core.Name.ScopedList.HasLength

---------------------------------------
-- horrible hack
import Core.Name.ScopedList as L

public export
0 LSizeOf : {0 a : Type} -> ScopedList a -> Type
LSizeOf xs = L.SizeOf xs

export
reverse : L.SizeOf xs -> L.SizeOf (reverse xs)
reverse (L.MkSizeOf n p) = L.MkSizeOf n (hasLengthReverse p)

%hide L.SizeOf
---------------------------------------

%hide Libraries.Data.SnocList.SizeOf.LSizeOf

public export
(<>>) : SizeOf {a} sx -> LSizeOf {a} ys -> LSizeOf (sx <>> ys)
MkSizeOf m p <>> MkSizeOf n q = MkSizeOf (m + n) (hlChips p q)
