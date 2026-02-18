import Data.Nat

%default total

f : n `LTE` m -> Void
f Z impossible
f (LTESucc x) = f x

x : Void
x = f $ LTEZero {right=Z}
