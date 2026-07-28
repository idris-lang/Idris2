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
