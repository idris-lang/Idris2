module Builtin

-- The most primitive data types; things which are used by desugaring

-- Totality assertions

||| Assert to the totality checker that the given expression will always
||| terminate.
%inline
public export
assert_total : {0 a : _} -> a -> a
assert_total x = x

||| Assert to the totality checker that y is always structurally smaller than x
||| (which is typically a pattern argument, and *must* be in normal form for
||| this to work).
||| @ x the larger value (typically a pattern argument)
||| @ y the smaller value (typically an argument to a recursive call)
%inline
public export
assert_smaller : {0 a, b : _} -> (x : a) -> (y : b) -> b
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
  MkPair : {0 a, b : Type} -> (1 x : a) -> (1 y : b) -> Pair a b

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

||| Dependent pairs aid in the construction of dependent types by providing
||| evidence that some value resides in the type.
|||
||| Formally, speaking, dependent pairs represent existential quantification -
||| they consist of a witness for the existential claim and a proof that the
||| property holds for it.
|||
||| @ a the value to place in the type.
||| @ p the dependent type that requires the value.
namespace DPair
  public export
  record DPair a (p : a -> Type) where
    constructor MkDPair
    fst : a
    snd : p fst

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
     Refl : {0 x : a} -> Equal x x

%name Equal prf

infix 9 ===, ~=~

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
                (0 rule : x = y) -> (1 val : p y) -> p x
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

||| Subvert the type checker.  This function is abstract, so it will not reduce
||| in the type checker.  Use it with care - it can result in segfaults or
||| worse!
public export
believe_me : a -> b
believe_me = prim__believe_me _ _

export partial
idris_crash : String -> a
idris_crash = prim__crash _
