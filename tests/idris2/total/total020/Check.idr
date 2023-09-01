%default total

data X : Type -> Type -> Type where
  B : b -> X a b
  R : X a b -> X b c -> X a c

[WithFunction] Functor (X a) where
  map f $ B x = B $ f x
  map f $ R x y = R x (map f y)

[WithInfix] Functor (X a) where
  map f $ B x = B $ f x
  map f $ R x y = R x (f <$> y)

[WithFoldMap] Foldable (X a) where

  foldr = ?some_foldr_1

  foldMap f $ B x   = f x
  foldMap f rlr@(R l r) = do
    let r' = map @{WithFunction} f r
    foldMap id $ assert_smaller rlr r'

[WithConcat] Foldable (X a) where

  foldr = ?some_foldr_2

  foldMap f $ B x   = f x
  foldMap f rlr@(R l r) = do
    let r' = map @{WithFunction} f r
    concat $ assert_smaller rlr r'
