module Libraries.Data.List.HasLength

import Data.Nat

import Data.List.HasLength

export
cast : {ys : _} -> (0 _ : List.length xs = List.length ys) -> HasLength m xs -> HasLength m ys
cast {ys = []}      eq Z = Z
cast {ys = y :: ys} eq (S p) = S (cast (injective eq) p)
