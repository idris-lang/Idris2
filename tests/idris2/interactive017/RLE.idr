module RLE

import Decidable.Equality

rep : Nat -> a -> List a

data RunLength : List a -> Type where
     Empty : RunLength []
     Run : (n : Nat) -> (x : a) -> (rest : RunLength more) ->
           RunLength (rep n x ++ more)

data Singleton : a -> Type where
     Val : (x : a) -> Singleton x

uncompress : RunLength xs -> Singleton xs












{-

rle : DecEq a => (xs : List a) -> RLE xs
rle [] = Empty
rle (x :: xs) with (rle xs)
  rle (x :: []) | Empty = Run 1 x Empty
  rle (x :: (rep n y ++ more)) | (Run n y comp) with (decEq x y)
    rle (y :: (rep n y ++ more)) | (Run n y comp) | (Yes Refl)
        = Run (S n) y comp
    rle (x :: (rep n y ++ more)) | (Run n y comp) | (No contra)
        = Run 1 x $ Run n y comp

data Singleton : a -> Type where
     Val : (x : a) -> Singleton x

uncompress : RLE xs -> Singleton xs

-- uncompress Empty = Val []
-- uncompress (Run n x comp)
--     = let Val rec = uncompress comp in
--           Val (rep n x ++ rec)

uncompressHelp : (x : a) -> RLE more -> (n : Nat) -> Singleton more -> Singleton (rep n x ++ more)
uncompressHelp x comp n (Val _) = Val (rep n x ++ more)

uncompress' : RLE xs -> Singleton xs
uncompress' Empty = Val []
uncompress' (Run n x comp)
    = let rec = uncompress' comp in
          uncompressHelp x comp n rec






















{-
rle [] = Empty
rle (x :: xs) with (rle xs)
  rle (x :: []) | Empty = Run 1 x Empty
  rle (x :: (rep n y ++ more)) | (Run n y comp) with (decEq x y)
    rle (y :: (rep n y ++ more)) | (Run n y comp) | (Yes Refl)
        = Run (S n) y comp
    rle (x :: (rep n y ++ more)) | (Run n y comp) | (No contra)
        = Run 1 x $ Run n y comp

uncompress Empty = Val []
uncompress (Run n x comp)
   = let Val uncomp = uncompress comp in
         Val (rep n x ++ uncomp)
-}
-}
