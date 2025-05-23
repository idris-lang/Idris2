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

  export infixr 6 `zip`

  ||| Combine three parameterised types by applying a function.
  ||| @ z the parameterised type
  ||| @ func the function to combine elements with
  zipWith3 : (func : a -> b -> c -> d) -> z a -> z b -> z c -> z d
  zipWith3 f = zipWith (uncurry f) .: zip

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
  unzipWith3 = mapSnd unzip .: unzipWith

  ||| Split a parameterised type of triplets into a triplet of parameterised
  ||| types.
  ||| @ z the parameterised type
  unzip3 : z (a, b, c) -> (z a, z b, z c)
  unzip3 = unzipWith3 id

public export
[Compose] Zippable f => Zippable g => Zippable (f . g) where
  zipWith f = zipWith $ zipWith f
  zipWith3 f = zipWith3 $ zipWith3 f
  unzipWith f = unzipWith $ unzipWith f
  unzipWith3 f = unzipWith3 $ unzipWith3 f

  zip = zipWith zip
  zip3 = zipWith3 zip3
  unzip = unzipWith unzip
  unzip3 = unzipWith3 unzip3

||| Variant of composing and decomposing using existing `Applicative` implementation.
|||
||| This implementation is lazy during unzipping.
||| Caution! It may repeat the whole original work, each time the unzipped elements are used.
|||
||| Please be aware that not every `Applicative` has the same semantics as `Zippable`.
||| Consider `List` as a simple example.
||| However, this implementation is applicable for lazy data types or deferred computations.
public export
[FromApplicative] Applicative f => Zippable f where
  zipWith f x y = [| f x y |]
  zipWith3 f x y z = [| f x y z |]

  unzip u = (map fst u, map snd u)
  unzip3 u = (map fst u, map (fst . snd) u, map (snd . snd) u)
  unzipWith f = unzip . map f
  unzipWith3 f = unzip3 . map f

 -- To be moved appropriately as soon as we have some module like `Data.Pair`, like other prelude types have.
public export
Semigroup a => Zippable (Pair a) where
  zipWith f (l, x) (r, y) = (l <+> r, f x y)
  zipWith3 f (l, x) (m, y) (r, z) = (l <+> m <+> r, f x y z)

  unzipWith f (l, x) = bimap (l,) (l,) (f x)
  unzipWith3 f (l, x) = bimap (l,) (bimap (l,) (l,)) (f x)
