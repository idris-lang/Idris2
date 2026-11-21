module Main

import Data.Seq.Unsized

-- Run with the contrib package: `idris2 --exec main Repro.idr -p contrib`

main : IO ()
main = do
  -- 1. `index` returns the wrong element.
  let ss = fromList [1 .. 15]
  for_ [0 .. 14] $ \i => printLn (index i ss)

  -- 2. A sequence made with `++` is split in the wrong place (snocTree keeps a
  --    wrong cached size). The length is right (20), the cut is not.
  let s = fromList [1 .. 18] ++ fromList [19, 20]
  printLn (length s, (take 19 s), (drop 19 s))


