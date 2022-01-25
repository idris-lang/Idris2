import Data.SnocList

iterateTR : Nat -> (a -> a) -> a -> List a
iterateTR n f = go n Lin
  where go : Nat -> SnocList a -> a -> List a
        go 0     sx _ = sx <>> Nil
        go (S k) sx v = go k (sx :< v) (f v)

main : IO ()
main = do
  printLn $ [1..4] >>= (\n => iterateTR n (+1) n)
  printLn . length $ [1..5000] >>= (\n => iterateTR n (+1) n)
