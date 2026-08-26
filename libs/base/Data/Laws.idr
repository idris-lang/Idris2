module Data.Laws

namespace Functor
  public export 0
  Identity : (f : Type -> Type) -> Functor f => Type
  Identity f = forall a . (x : f a) -> map id x = x

  public export 0
  Composition : (f : Type -> Type) -> Functor f => Type
  Composition f =
    forall a, b, c . (x : f a) -> (g : a -> b) -> (h : b -> c) -> map h (map g x) = map (h . g) x

namespace Applicative
  public export 0
  Identity : (f : Type -> Type) -> Applicative f => Type
  Identity f = forall a . (x : f a) -> pure id <*> x = x

  public export 0
  Homomorphism : (f : Type -> Type) -> Applicative f => Type
  Homomorphism f = forall a, b . (x : a) -> (g : a -> b) -> pure g <*> pure x = pure {f} (g x)

  public export 0
  Interchange : (f : Type -> Type) -> Applicative f => Type
  Interchange f = forall a, b . (g : f (a -> b)) -> (x : a) -> g <*> pure x = pure ($ x) <*> g

  public export 0
  Composition : (f : Type -> Type) -> Applicative f => Type
  Composition f =
    forall a, b, c .
    (h : f (b -> c)) ->
    (g : f (a -> b)) ->
    (x : f a) ->
    pure (.) <*> h <*> g <*> x = h <*> (g <*> x)
