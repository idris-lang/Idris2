module Data.DPair

%default total

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
  data Exists : (this : type -> Type) -> Type where
    Evidence : (0 value : type)
            -> (prf : this value)
            -> Exists this

  ||| Return the type-level value (evidence) required by the dependent type.
  |||
  ||| We need to be in the Erased setting for this to work.
  |||
  ||| @type The type-level value's type.
  ||| @pred The dependent type that requires an instance of `type`.
  ||| @prf  That there is a value that satisfies `prf`.
  public export
  0
  fst : {0 type : Type}
     -> {0 pred : type -> Type}
     -> (1 prf  : Exists pred)
     -> type
  fst (Evidence value _) = value

  ||| Return the dependently typed value.
  |||
  ||| @type The type-level value's type.
  ||| @pred The dependent type that requires an instance of `type`.
  ||| @prf  That there is a value that satisfies `prf`.
  public export
  snd : {0 type : Type}
     -> {0 pred : type -> Type}
     -> (1 prf  : Exists pred)
     -> pred (Exists.fst prf)
  snd (Evidence value prf) = prf

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
  data Subset : (type : Type)
             -> (pred : type -> Type)
             -> Type
    where
      Element : (value : type)
             -> (0 prf : pred value)
             -> Subset type pred

  ||| Return the type-level value (evidence) required by the dependent type.
  |||
  ||| @type The type-level value's type.
  ||| @pred The dependent type that requires an instance of `type`.
  ||| @prf  That there is a value that satisfies `prf`.
  public export
  fst : {0 type : Type}
     -> {0 pred : type -> Type}
     -> (1 prf  : Subset type pred)
     -> type
  fst (Element value prf) = value

  ||| Return the dependently typed value.
  |||
  ||| We need to be in the erased setting for this to work.
  |||
  ||| @type The type-level value's type.
  ||| @pred The dependent type that requires an instance of `type`.
  ||| @prf  That there is a value that satisfies `prf`.
  public export
  0
  snd : {0 type : Type}
     -> {0 pred : type -> Type}
     -> (1 value : Subset type pred)
     -> pred (Subset.fst value)
  snd (Element value prf) = prf
