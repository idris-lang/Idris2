import Data.Vect

using (Show a, Eq a)
  foo : a -> String
  foo x = show x ++ show x

  bar : Int -> Int
  bar x = x + x

using (xs : Vect n a, n : Nat) -- get reordered in dependency order by
                               -- the usual implicit rules
  baz : xs = xs

data Test : Type -> Type -> Type where

using (Test a b)
  needle : a -> b -> ()
  nardle : a -> ()
  noo : b -> ()
