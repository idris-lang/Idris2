module Builtin

-- The most primitive data types; things which are used by desugaring

-- Totality assertions

||| Assert to the totality checker that the given expression will always
||| terminate.
|||
||| The multiplicity of its argument is 1, so `assert_total` won't affect how
||| many times variables are used. If you're not writing a linear function,
||| this doesn't make a difference.
|||
||| Note: assert_total can reduce at compile time, if required for unification,
||| which might mean that it's no longer guarded a subexpression. Therefore,
||| it is best to use it around the smallest possible subexpression.
%inline
public export
assert_total : (1 _ : a) -> a
assert_total x = x

||| Assert to the totality checker that y is always structurally smaller than x
||| (which is typically a pattern argument, and *must* be in normal form for
||| this to work).
|||
||| The multiplicity of x is 0, so in a linear function, you can pass values to
||| x even if they have already been used.
||| The multiplicity of y is 1, so `assert_smaller` won't affect how many times
||| its y argument is used.
||| If you're not writing a linear function, the multiplicities don't make a
||| difference.
|||
||| @ x the larger value (typically a pattern argument)
||| @ y the smaller value (typically an argument to a recursive call)
%inline
public export
assert_smaller : (0 x : a) -> (1 y : b) -> b
assert_smaller x y = y

-- Unit type and pairs

||| The canonical single-element type, also known as the trivially true
||| proposition.
public export
data Unit =
  ||| The trivial constructor for `()`.
  MkUnit

||| The non-dependent pair type, also known as conjunction.
public export
data Pair : Type -> Type -> Type where
  ||| A pair of elements.
  ||| @ a the left element of the pair
  ||| @ b the right element of the pair
  MkPair : {0 a, b : Type} -> (x : a) -> (y : b) -> Pair a b

||| Return the first element of a pair.
public export
fst : {0 a, b : Type} -> (a, b) -> a
fst (x, y) = x

||| Return the second element of a pair.
public export
snd : {0 a, b : Type} -> (a, b) -> b
snd (x, y) = y

-- This directive tells auto implicit search what to use to look inside pairs
%pair Pair fst snd

infix 5 #

||| A pair type where each component is linear
public export
data LPair : Type -> Type -> Type where
     (#) : (1 _ : a) -> (1 _ : b) -> LPair a b

namespace DPair
  ||| Dependent pairs aid in the construction of dependent types by providing
  ||| evidence that some value resides in the type.
  |||
  ||| Formally, speaking, dependent pairs represent existential quantification -
  ||| they consist of a witness for the existential claim and a proof that the
  ||| property holds for it.
  |||
  ||| @ a the value to place in the type.
  ||| @ p the dependent type that requires the value.
  public export
  record DPair a (p : a -> Type) where
    constructor MkDPair
    fst : a
    snd : p fst

  ||| A dependent variant of LPair, pairing a result value with a resource
  ||| that depends on the result value
  public export
  data Res : (a : Type) -> (a -> Type) -> Type where
       (#) : (val : a) -> (1 r : t val) -> Res a t

-- The empty type

||| The empty type, also known as the trivially false proposition.
|||
||| Use `void` or `absurd` to prove anything if you have a variable of type
||| `Void` in scope.
public export
data Void : Type where

-- Equality

public export
data Equal : forall a, b . a -> b -> Type where
     [search a b]
     Refl : {0 x : a} -> Equal x x

%name Equal prf

infix 6 ===, ~=~

-- An equality type for when you want to assert that each side of the
-- equality has the same type, but there's not other evidence available
-- to help with unification
public export
(===) : (x : a) -> (y : a) -> Type
(===) = Equal

||| Explicit heterogeneous ("John Major") equality.  Use this when Idris
||| incorrectly chooses homogeneous equality for `(=)`.
||| @ a the type of the left side
||| @ b the type of the right side
||| @ x the left side
||| @ y the right side
public export
(~=~) : (x : a) -> (y : b) -> Type
(~=~) = Equal

||| Perform substitution in a term according to some equality.
|||
||| Like `replace`, but with an explicit predicate, and applying the rewrite in
||| the other direction, which puts it in a form usable by the `rewrite` tactic
||| and term.
%inline
public export
rewrite__impl : {0 x, y : a} -> (0 p : _) ->
                (0 rule : x = y) -> (val : p y) -> p x
rewrite__impl p Refl prf = prf

%rewrite Equal rewrite__impl

||| Perform substitution in a term according to some equality.
%inline
public export
replace : forall x, y, p . (0 rule : x = y) -> p x -> p y
replace Refl prf = prf

||| Symmetry of propositional equality.
%inline
public export
sym : (0 rule : x = y) -> y = x
sym Refl = Refl

||| Transitivity of propositional equality.
%inline
public export
trans : forall a, b, c . (0 l : a = b) -> (0 r : b = c) -> a = c
trans Refl Refl = Refl

||| Injectivity of MkDPair (first components)
export
mkDPairInjectiveFst : MkDPair a pa === MkDPair b qb -> a === b
mkDPairInjectiveFst Refl = Refl

||| Injectivity of MkDPair (snd components)
export
mkDPairInjectiveSnd : MkDPair a pa === MkDPair a qa -> pa === qa
mkDPairInjectiveSnd Refl = Refl

||| Subvert the type checker.  This function is abstract, so it will not reduce
||| in the type checker.  Use it with care - it can result in segfaults or
||| worse!
public export
believe_me : a -> b
believe_me = prim__believe_me _ _

||| Assert to the usage checker that the given function uses its argument linearly.
public export
assert_linear : (1 f : a -> b) -> (1 val : a) -> b
assert_linear = believe_me id
  where
    id : (1 f : a -> b) -> a -> b
    id f = f


export partial
idris_crash : String -> a
idris_crash = prim__crash _

public export %inline
delay : a -> Lazy a
delay x = Delay x

public export %inline
force : Lazy a -> a
force x = Force x

%stringLit fromString

||| Interface for types that can be constructed from string literals.
public export
interface FromString ty where
  ||| Conversion from String.
  fromString : String -> ty

%allow_overloads fromString

%inline
public export
FromString String where
  fromString s = s

%defaulthint
%inline
public export
defaultString : FromString String
defaultString = %search
