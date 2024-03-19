module Test

import Test2

%hide Test2.infixr.(@>)

infixl 9 @>

(@>) : a -> b -> (a, b)
(@>) = MkPair

test : 3 @> 2 @> 1 === (3 @> 2) @> 1
test = Refl
