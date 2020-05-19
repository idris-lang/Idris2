module Bifunctor

||| Bifunctors
||| @p The action of the Bifunctor on pairs of objects
public export
interface Bifunctor (p : Type -> Type -> Type) where
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = first f . second g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| first (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  first : (a -> b) -> p a c -> p b c
  first = flip bimap id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| second reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  second : (a -> b) -> p c a -> p c b
  second = bimap id

implementation Bifunctor Either where
  bimap f _ (Left  a) = Left  $ f a
  bimap _ g (Right b) = Right $ g b

public export
implementation Bifunctor Pair where
  bimap f g (a, b) = (f a, g b)
