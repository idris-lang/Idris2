module Libraries.Data.List01

import Data.List

public export
data List01 : (nonEmpty : Bool) -> Type -> Type where
  Nil  : List01 False a
  (::) : a -> List01 ne a -> List01 True a

public export
fromList : (xs : List a) -> List01 (isCons xs) a
fromList [] = []
fromList (x :: xs) = x :: fromList xs

public export
(++) : List01 nel a -> List01 ner a -> List01 (nel || ner) a
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

public export
length : (xs : List01 ne a) -> Nat
length [] = 0
length (_ :: xs) = S (length xs)

public export
forget : List01 ne a -> List a
forget [] = []
forget (x :: xs) = x :: forget xs

public export
Functor (List01 ne) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

export
Show a => Show (List01 ne a) where
    show = show . forget

export
Foldable (List01 ne) where
  foldr c n [] = n
  foldr c n (x :: xs) = c x (foldr c n xs)

  foldl f q [] = q
  foldl f q (x :: xs) = foldl f (f q x) xs

  null [] = True
  null (_ :: _) = False

  toList = forget

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral
