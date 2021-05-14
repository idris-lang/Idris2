module Data.Contravariant

infixl 4 >$, >$<, >&<, $<

||| Contravariant functors
public export
interface Contravariant (0 f : Type -> Type) where
  contramap : (a -> b) -> f b -> f a

  (>$) : b -> f b -> f a
  v >$ fb = contramap (const v) fb

||| If `f` is both `Functor` and `Contravariant` then by the time you factor in the
||| laws of each of those classes, it can't actually use its argument in any
||| meaningful capacity.
public export %inline
phantom : (Functor f, Contravariant f) => f a -> f b
phantom fa = () >$ (fa $> ())

||| This is an infix alias for `contramap`.
public export %inline
(>$<) : Contravariant f => (a -> b) -> f b -> f a
(>$<) = contramap

||| This is an infix version of `contramap` with the arguments flipped.
public export %inline
(>&<) : Contravariant f => f b -> (a -> b) -> f a
(>&<) = flip contramap

||| This is `>$` with its arguments flipped.
public export %inline
($<) : Contravariant f => f b -> b -> f a
($<) = flip (>$)

||| Composition of `Contravariant` is a `Functor`.
public export
[Compose] (Contravariant f, Contravariant g) => Functor (f . g) where
  map = contramap . contramap

||| Composition of a `Functor` and a `Contravariant` is a `Contravariant`.
public export
[ComposeFC] (Functor f, Contravariant g) => Contravariant (f . g) where
  contramap = map . contramap

||| Composition of a `Contravariant` and a `Functor` is a `Contravariant`.
public export
[ComposeCF] (Contravariant f, Functor g) => Contravariant (f . g) where
  contramap = contramap . map
