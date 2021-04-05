module Libraries.Text.Distance.Levenshtein

import Data.List
import Data.Maybe
import Data.Strings
import Libraries.Data.IOMatrix
import Libraries.Data.List.Extra

%default total

||| Self-evidently correct but O(3 ^ (min mn)) complexity
spec : String -> String -> Nat
spec a b = loop (fastUnpack a) (fastUnpack b) where

  loop : List Char -> List Char -> Nat
  loop [] ys = length ys -- deletions
  loop xs [] = length xs -- insertions
  loop (x :: xs) (y :: ys)
    = if x == y then loop xs ys -- match
      else 1 + minimum [ loop (x :: xs) ys -- insert y
                       , loop xs (y :: ys) -- delete x
                       , loop xs ys        -- substitute y for x
                       ]

||| Dynamic programming
export
compute : HasIO io => String -> String -> io Nat
compute a b = assert_total $ do
  let w = strLength a
  let h = strLength b
  -- In mat[i][j], we store the distance between
  -- * the suffix of a of size i
  -- * the suffix of b of size j
  -- So we need a matrix of size (|a|+1) * (|b|+1)
  mat <- new (w+1) (h+1)
  -- Whenever one of the two suffixes of interest is empty, the only
  -- winning move is to:
  -- * delete all of the first
  -- * insert all of the second
  -- i.e. the cost is the length of the non-zero suffix
  for_ [0..w] $ \ i => write mat i 0 i -- deletions
  for_ [0..h] $ \ j => write mat 0 j j -- insertions

  -- We introduce a specialised `read` for ease of use
  let get = \i, j => case !(read {io} mat i j) of
        Nothing => idris_crash "INTERNAL ERROR: Badly initialised matrix"
        Just n => pure n

  -- We fill the matrix from the bottom up, using the same formula we used
  -- in the specification's `loop`.
  for_ [1..h] $ \ j => do
    for_ [1..w] $ \ i => do
      -- here we change Levenshtein slightly so that we may only substitute
      -- alpha / numerical characters for similar ones. This avoids suggesting
      -- "#" as a replacement for an out of scope "n".
      let cost = let c = strIndex a (i-1)
                     d = strIndex b (j-1)
                 in if c == d then 0 else
                    if isAlpha c && isAlpha d then 1 else
                    if isDigit c && isDigit d then 1 else 2
      write mat i j $
        minimum [ 1    + !(get i (j-1))     -- insert y
                , 1    + !(get (i-1) j)     -- delete x
                , cost + !(get (i-1) (j-1)) -- equal or substitute y for x
                ]

  -- Once the matrix is fully filled, we can simply read the top right corner
  integerToNat . cast <$> get w h
