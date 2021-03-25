module Libraries.Text.Distance.Levenshtein

import Data.List
import Data.Maybe
import Data.Strings
import Libraries.Data.IOMatrix
import Libraries.Data.List.Extra

%default total

||| Self-evidently correct but O(3 ^ (min mn)) complexity
spec : String -> String -> Int
spec a b = loop (fastUnpack a) (fastUnpack b) where

  loop : List Char -> List Char -> Int
  loop [] ys = cast (length ys) -- additions
  loop xs [] = cast (length xs) -- additions
  loop (x :: xs) (y :: ys)
    = if x == y then loop xs ys -- match
      else 1 + minimum [ loop (x :: xs) ys -- insert y
                       , loop xs (y :: ys) -- delete x
                       , loop xs ys        -- substitute y for x
                       ]

||| Dynamic programming
compute : String -> String -> IO Int
compute a b = assert_total $ do
  let w = strLength a
  let h = strLength b
  mat <- new (w+1) (h+1)
  let get = \i, j => case !(read {io = IO} mat i j) of
        Nothing => idris_crash "INTERNAL ERROR: Badly initialised matrix"
        Just n => pure n
  for_ [0..w] $ \ i => write mat i 0 i -- additions
  for_ [0..h] $ \ j => write mat 0 j j -- additions
  for_ [1..h] $ \ j => do
    for_ [1..w] $ \ i => do
      let cost = if strIndex a (i-1) == strIndex b (j-1) then 0 else 1
      write mat i j $
        minimum [ 1    + !(get i (j-1))     -- insert y
                , 1    + !(get (i-1) j)     -- delete x
                , cost + !(get (i-1) (j-1)) -- equal or substitute y for x
                ]
  get w h
