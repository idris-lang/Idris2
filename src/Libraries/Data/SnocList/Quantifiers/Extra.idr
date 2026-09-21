module Libraries.Data.SnocList.Quantifiers.Extra

import Data.SnocList
import Data.SnocList.Quantifiers
import Decidable.Equality

%default total

export
tail : All p (xs :< x) -> All p xs
tail (pxs :< _) = pxs

export
head : All p (xs :< x) -> p x
head (_ :< px) = px

export
tabulate : ((x : a) -> p x) -> (xs : SnocList a) -> All p xs
tabulate f [<] = [<]
tabulate f (xs :< x) = tabulate f xs :< f x
