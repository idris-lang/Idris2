import Data.Fin

-- This tests that `Show`, `Eq`, and `Ord` for `Fin`
-- run in constant time (Strictly speaking, it's O(log n) with
-- a large base).
--
-- It also verifies that `last` and `finToNat` run in O(1)
-- (both should be removed by the identity optimizer during
-- compilation)
main : IO ()
main = do
  let largeNat := the Nat 0xffff_ffff_ffff_ffff
      fin      := last {n = largeNat}
  printLn fin               -- `Show` for `Fin` runs in O(1)
  printLn (fin == fin)      -- `Eq` for `Fin` runs in O(1)
  printLn (compare fin fin) -- `Ord` for `Fin` runs in O(1)
