module Data.DPair

%default total

namespace DPair

  public export
  curry : {0 p : a -> Type} -> ((x : a ** p x) -> c) -> (x : a) -> p x -> c
  curry f x y = f (x ** y)

  public export
  uncurry : {0 p : a -> Type} -> ((x : a) -> p x -> c) -> (x : a ** p x) -> c
  uncurry f s = f s.fst s.snd

  public export
  bimap : {0 p : a -> Type} -> {0 q : b -> Type} -> (f : a -> b) -> (forall x. p x -> q (f x)) -> (x : a ** p x) -> (y : b ** q y)
  bimap f g (x ** y) = (f x ** g y)

namespace Exists

  public export
  curry : {0 p : a -> Type} -> (Exists a p -> c) -> ({0 x : a} -> p x -> c)
  curry f = f . Evidence _

  public export
  uncurry : {0 p : a -> Type} -> ({0 x : a} -> p x -> c) -> Exists a p -> c
  uncurry f ex = f ex.snd

  export
  evidenceInjectiveFst : Evidence x p = Evidence y q -> x = y
  evidenceInjectiveFst Refl = Refl

  export
  evidenceInjectiveSnd : Evidence x p = Evidence x q -> p = q
  evidenceInjectiveSnd Refl = Refl

  public export
  bimap : (0 f : a -> b) -> (forall x. p x -> q (f x)) -> Exists a p -> Exists b q
  bimap f g (Evidence x y) = Evidence (f x) (g y)

namespace Subset

  public export
  curry : {0 p : a -> Type} -> (Subset a p -> c) -> (x : a) -> (0 _ : p x) -> c
  curry f x y = f $ Element x y

  public export
  uncurry : {0 p : a -> Type} -> ((x : a) -> (0 _ : p x) -> c) -> Subset a p -> c
  uncurry f s = f s.fst s.snd

  export
  elementInjectiveFst : Element x p = Element y q -> x = y
  elementInjectiveFst Refl = Refl

  export
  elementInjectiveSnd : Element x p = Element x q -> p = q
  elementInjectiveSnd Refl = Refl

  public export
  bimap : (f : a -> b) -> (0 _ : forall x. p x -> q (f x)) -> Subset a p -> Subset b q
  bimap f g (Element x y) = Element (f x) (g y)

  public export
  Eq type => Eq (Subset type pred) where
    (==) = (==) `on` fst

  public export
  Ord type => Ord (Subset type pred) where
    compare = compare `on` fst

  ||| This Show implementation replaces the (erased) invariant
  ||| with an underscore.
  export
  Show type => Show (Subset type pred) where
    showPrec p (Element v _) = showCon p "Element" $ showArg v ++ " _"
