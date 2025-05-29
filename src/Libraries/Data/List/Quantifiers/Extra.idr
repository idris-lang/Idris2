module Libraries.Data.List.Quantifiers.Extra

import Data.List
import Data.List.Quantifiers
import Decidable.Equality

%default total

export
lookup : {xs : List a} -> DecEq a => (v : a) -> All p xs -> Maybe (p v)
lookup v [] = Nothing
lookup v (px :: pxs)
  = case decEq (head xs) v of
      No _ => lookup v pxs
      Yes Refl => Just px

-- TODO: delete this function after 0.7.1 is released
-- as it now exists in base's Data.List.Quantifiers
export
(++) : All p xs -> All p ys -> All p (xs ++ ys)
[] ++ pys = pys
(px :: pxs) ++ pys = px :: (Extra.(++) pxs pys)

export
tabulate : ((x : a) -> p x) -> (xs : List a) -> All p xs
tabulate f [] = []
tabulate f (x :: xs) = f x :: tabulate f xs

-- TODO: delete this function after 0.7.1 is released
-- as it now exists in base's Data.List.Quantifiers
export
head : All p (x :: xs) -> p x
head (px :: _) = px

-- TODO: delete this function after 0.7.1 is released
-- as it now exists in base's Data.List.Quantifiers
export
tail : All p (x :: xs) -> All p xs
tail (_ :: pxs) = pxs
