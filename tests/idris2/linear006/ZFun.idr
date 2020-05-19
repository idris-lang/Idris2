import Data.Fin

foo : Fin 10
foo = 5

0 test : Fin k -> Nat
test i = k

0 baz : Nat
baz = test foo -- fine!

bar : Nat
bar = test foo -- bad!

