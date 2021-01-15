module Data.DPair

%default total

namespace DPair

  public export
  curry : {0 p : a -> Type} -> ((x : a ** p x) -> c) -> (x : a) -> p x -> c
  curry f x y = f (x ** y)

  public export
  uncurry : {0 p : a -> Type} -> ((x : a) -> p x -> c) -> (x : a ** p x) -> c
  uncurry f s = f s.fst s.snd

namespace Exists

  ||| A dependent pair in which the first field (witness) should be
  ||| erased at runtime.
  |||
  ||| We can use `Exists` to construct dependent types in which the
  ||| type-level value is erased at runtime but used at compile time.
  ||| This type-level value could represent, for instance, a value
  ||| required for an intrinsic invariant required as part of the
  ||| dependent type's representation.
  |||
  ||| @type The type of the type-level value in the proof.
  ||| @this The dependent type that requires an instance of `type`.
  public export
  record Exists {0 type : _} this where
    constructor Evidence
    0 fst : type
    snd : this fst

  public export
  curry : {0 p : a -> Type} -> (Exists {type=a} p -> c) -> ({0 x : a} -> p x -> c)
  curry f = f . Evidence _

  public export
  uncurry : {0 p : a -> Type} -> ({0 x : a} -> p x -> c) -> Exists {type=a} p -> c
  uncurry f ex = f ex.snd

namespace Subset

  ||| A dependent pair in which the second field (evidence) should not
  ||| be required at runtime.
  |||
  ||| We can use `Subset` to provide extrinsic invariants about a
  ||| value and know that these invariants are erased at
  ||| runtime but used at compile time.
  |||
  ||| @type The type-level value's type.
  ||| @pred The dependent type that requires an instance of `type`.
  public export
  record Subset type pred where
    constructor Element
    fst : type
    0 snd : pred fst

  public export
  curry : {0 p : a -> Type} -> (Subset a p -> c) -> (x : a) -> (0 _ : p x) -> c
  curry f x y = f $ Element x y

  public export
  uncurry : {0 p : a -> Type} -> ((x : a) -> (0 _ : p x) -> c) -> Subset a p -> c
  uncurry f s = f s.fst s.snd
