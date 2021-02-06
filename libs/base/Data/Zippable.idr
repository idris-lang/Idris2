module Data.Zippable

%default total

---------------------------
-- Zips and unzips --
---------------------------

||| The `Zippable` interface describes how you can combine and split the
||| elements in a parameterised type.
||| @ z the parameterised type
public export
interface Zippable z where
  ||| Combine two parameterised types by applying a function.
  ||| @ z the parameterised type
  ||| @ func the function to combine elements with
  zipWith : (func : a -> b -> c) -> z a -> z b -> z c

  ||| Combine two parameterised types into a parameterised type of pairs.
  ||| @ z the parameterised type
  zip : z a -> z b -> z (a, b)
  zip = zipWith (,)

  infixr 6 `zip`

  ||| Combine three parameterised types by applying a function.
  ||| @ z the parameterised type
  ||| @ func the function to combine elements with
  zipWith3 : (func : a -> b -> c -> d) -> z a -> z b -> z c -> z d

  ||| Combine three parameterised types into a parameterised type of triplets.
  ||| @ z the parameterised type
  zip3 : z a -> z b -> z c -> z (a, b, c)
  zip3 = zipWith3 (,,)

  ||| Split a parameterised type by applying a function into a pair of
  ||| parameterised types.
  ||| @ z the parameterised type
  ||| @ func the function to split elements with
  unzipWith : (func : a -> (b, c)) -> z a -> (z b, z c)

  ||| Split a parameterised type of pairs into a pair of parameterised types.
  ||| @ z the parameterised type
  unzip : z (a, b) -> (z a, z b)
  unzip = unzipWith id

  ||| Split a parameterised type by applying a function into a triplet of
  ||| parameterised types.
  ||| @ z the parameterised type
  ||| @ func the function to split elements with
  unzipWith3 : (func : a -> (b, c, d)) -> z a -> (z b, z c, z d)

  ||| Split a parameterised type of triplets into a triplet of parameterised
  ||| types.
  ||| @ z the parameterised type
  unzip3 : z (a, b, c) -> (z a, z b, z c)
  unzip3 = unzipWith3 id
