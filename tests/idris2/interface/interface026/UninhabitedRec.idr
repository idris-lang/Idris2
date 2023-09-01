module UninhabitedRec

import Data.Nat
import Data.List.Elem

ff : Uninhabited (a, b) => Int
ff = 4

callFGood : Int
callFGood = ff {b = (Left 4 = Right 4)} {a = 5 = 5}

------------------

data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : (0 _ : Uninhabited $ x === z) => Lookup z xys -> Lookup z $ (x, y)::xys

fff : (xs : List (Nat, String)) -> (n : Nat) -> (0 _ : Lookup n xs) => String

xxs : List (Nat, String)
xxs = [(1, "one"), (2, "two"), (4, "four")]

lkup1Good : String
lkup1Good = fff xxs 1

lkup2Good : String
lkup2Good = fff xxs 2

lkup3Bad : String
lkup3Bad = fff xxs 3

------------------

data Uniq : Type -> Type

toList : Uniq a -> List a

data Uniq : Type -> Type where
  Nil  : Uniq a
  (::) : (x : a) -> (xs : Uniq a) -> Uninhabited (Elem x $ toList xs) => Uniq a

toList [] = []
toList (x::xs) = x :: toList xs

uniqGood : Uniq Nat
uniqGood = [1, 2, 3]

uniqBad : Uniq Nat
uniqBad = [1, 2, 1]
