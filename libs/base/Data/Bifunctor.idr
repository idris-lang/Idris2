module Data.Bifunctor

||| Bifunctors
||| @f The action of the Bifunctor on pairs of objects
public export
interface Bifunctor f where
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  bimap : (a -> c) -> (b -> d) -> f a b -> f c d
  bimap f g = mapFst f . mapSnd g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| mapFst (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  mapFst : (a -> c) -> f a b -> f c b
  mapFst f = bimap f id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| mapSnd reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  mapSnd : (b -> d) -> f a b -> f a d
  mapSnd = bimap id

public export
mapHom : Bifunctor f => (a -> b) -> f a a -> f b b
mapHom f = bimap f f

public export
Bifunctor Pair where
  bimap f g (x, y) = (f x, g y)

public export
Bifunctor Either where
  bimap f _ (Left x) = Left (f x)
  bimap _ g (Right y) = Right (g y)
