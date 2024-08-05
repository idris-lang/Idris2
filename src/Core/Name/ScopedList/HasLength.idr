module Core.Name.ScopedList.HasLength

import Data.Nat

import Libraries.Data.SnocList.HasLength

---------------------------------------
-- horrible hack
import Core.Name.ScopedList as L

public export
LHasLength : Nat -> ScopedList a -> Type
LHasLength = L.HasLength
%hide L.HasLength
---------------------------------------

%hide Libraries.Data.SnocList.HasLength.LHasLength

export
hlChips : HasLength m sx -> LHasLength n ys -> LHasLength (m + n) (sx <>> ys)
hlChips Z y = y
hlChips {m = S m} {n} (S x) y
  = rewrite plusSuccRightSucc m n in
    hlChips x (S y)
