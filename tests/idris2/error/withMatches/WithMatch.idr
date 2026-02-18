import Data.List
import Data.Nat
import Control.WellFounded

%default total

-- Verify correct FC for "With clause does not match parent"

-- From issue 3317
f :  Eq a => (xs : List a) -> { auto p : NonEmpty xs } -> Nat
f (x::xs) with (sizeAccessible xs)
  f [_] | _ = 1
  f (x::y::zs) | Access r =
    if x /= y
       then f (x::zs) | r _ reflexive
       else S (f (x::zs)) | r _ reflexive

-- IAlternative case
test : () -> Nat -> Nat
test () x with (x)
  test () x | Z = Z
  test () x | S k = test (Z = Z) x | k

-- IPrimVal case
test2 : (x : Int) -> x = 1 -> Nat -> Nat
test2 1 Refl y with (y)
  test2 1 Refl y | 0 = 42
  test2 1 Refl y | S k = test2 2 Refl y | k
