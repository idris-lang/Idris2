module Libraries.Data.List01.Quantifiers

import Data.DPair
import Libraries.Data.List01

%default total

namespace All

  ||| A proof that all elements of a list satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `List`.
  public export
  data All : (0 p : a -> Type) -> List01 ne a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : List01 ne a} -> p x -> All p xs -> All p (x :: xs)

  ||| Push in the property from the list level with element level
  public export
  pushIn : (xs : List01 ne a) -> (0 _ : All p xs) -> List01 ne $ Subset a p
  pushIn []        []      = []
  pushIn (x :: xs) (p::ps) = Element x p :: pushIn xs ps

  ||| Pull the elementwise property out to the list level
  public export
  pullOut : (xs : List01 ne $ Subset a p) -> Subset (List01 ne a) (All p)
  pullOut [] = Element [] []
  pullOut (Element x p :: xs) = bimap (x ::) (p ::) $ pullOut xs
