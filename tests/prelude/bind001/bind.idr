import Data.SnocList

iterateTR : Nat -> (a -> a) -> a -> List a
iterateTR n f = go n Lin
  where go : Nat -> SnocList a -> a -> List a
        go 0     sx _ = sx <>> Nil
        go (S k) sx v = go k (sx :< v) (f v)

%transform "listFoldMap" foldMap {t = List} {m = List _} = flip listBind

%transform "listConcatMap" concatMap {t = List} {m = List _} = flip listBind

%transform "listConcat" concat {t = List} {a = List _} = flip listBind id

main : IO ()
main = do
  -- this checks that *bind* still behaves correctly
  printLn $ [1..4] >>= (\n => iterateTR n (+1) 1)
  -- this verifies that *bind* runs in linear time
  printLn . length $ [1..5000] >>= (\n => iterateTR n (+1) n)
  -- here, we check that the transform rules apply
  printLn . length $ foldMap {t = List} (\n => iterateTR n (+1) n) [1..2000]
  printLn . length $ concatMap (\n => iterateTR n (+1) n) [1..2000]
  printLn . length . concat $ map (\n => iterateTR n (+1) n) [1..2000]
