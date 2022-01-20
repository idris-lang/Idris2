module RLE

import Data.List
import Data.Singleton
import Decidable.Equality

%default total

data RunLength : List a -> Type where
     Empty : RunLength []
     Run : (n : Nat)
        -> (x : a)
        -> (rest : RunLength more)
        -> RunLength (replicate n x ++ more)

uncompress : RunLength xs -> Singleton xs
uncompress Empty = [| [] |]
uncompress (Run n x comp) = [| (pure $ replicate n x) ++ uncompress comp |]

rle : DecEq a => (xs : List a) -> RunLength xs
rle [] = Empty
rle (x :: xs) with (rle xs)
  rle (x :: []) | Empty = Run 1 x Empty
  rle (x :: (replicate n y ++ more)) | (Run n y rest) = case decEq x y of
    Yes Refl => Run (S n) y rest
    No contra => Run 1 x (Run n y rest)
