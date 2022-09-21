||| Defines well-founded induction and recursion.
|||
||| Induction is way to consume elements of recursive types where each step of
||| the computation has access to the previous steps.
||| Normally, induction is structural: the previous steps are the children of
||| the current element.
||| Well-founded induction generalises this as follows: each step has access to
||| any value that is less than the current element, based on a relation.
|||
||| Well-founded induction is implemented in terms of accessibility: an element
||| is accessible (with respect to a given relation) if every element less than
||| it is also accessible. This can only terminate at minimum elements.
|||
||| This corresponds to the idea that for a computation to terminate, there
||| must be a finite path to an element from which there is no way to recurse.
|||
||| Many instances of well-founded induction are actually induction over
||| natural numbers that are derived from the elements being inducted over. For
||| this purpose, the `Sized` interface and related functions are provided.
module Control.WellFounded

import Control.Relation
import Data.Nat

%default total

||| A value is accessible if everything smaller than it is also accessible.
public export
data Accessible : (rel : a -> a -> Type) -> (x : a) -> Type where
  Access : (rec : (y : a) -> rel y x -> Accessible rel y) ->
           Accessible rel x

||| A relation is well-founded if every element is accessible.
public export
interface WellFounded a rel where
  wellFounded : (x : a) -> Accessible rel x

||| Simply-typed recursion based on accessibility.
|||
||| The recursive step for an element has access to all elements smaller than
||| it. The recursion will therefore halt when it reaches a minimum element.
|||
||| This may sometimes improve type-inference, compared to `accInd`.
export
accRec : {0 rel : (arg1 : a) -> (arg2 : a) -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
         (z : a) -> (0 acc : Accessible rel z) -> b
accRec step z (Access f) =
  step z $ \yarg, lt => accRec step yarg (f yarg lt)

||| Depedently-typed induction based on accessibility.
|||
||| The recursive step for an element has access to all elements smaller than
||| it. The recursion will therefore halt when it reaches a minimum element.
export
accInd : {0 rel : a -> a -> Type} -> {0 P : a -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
         (z : a) -> (0 acc : Accessible rel z) -> P z
accInd step z (Access f) =
  step z $ \y, lt => accInd step y (f y lt)

||| Simply-typed recursion based on well-founded-ness.
|||
||| This is `accRec` applied to accessibility derived from a `WellFounded`
||| instance.
export
wfRec : (0 _ : WellFounded a rel) =>
        (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
        a -> b
wfRec step x = accRec step x (wellFounded {rel} x)

||| Depedently-typed induction based on well-founded-ness.
|||
||| This is `accInd` applied to accessibility derived from a `WellFounded`
||| instance.
export
wfInd : (0 _ : WellFounded a rel) => {0 P : a -> Type} ->
        (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
        (myz : a) -> P myz
wfInd step myz = accInd step myz (wellFounded {rel} myz)

||| Types that have a concept of size. The size must be a natural number.
public export
interface Sized a where
  constructor MkSized
  total size : a -> Nat

||| A relation based on the size of the values.
public export
Smaller : Sized a => a -> a -> Type
Smaller = \x, y => size x `LT` size y

||| Values that are accessible based on their size.
public export
SizeAccessible : Sized a => a -> Type
SizeAccessible = Accessible Smaller

||| Any value of a sized type is accessible, since naturals are well-founded.
export
sizeAccessible : Sized a => (x : a) -> SizeAccessible x
sizeAccessible x = Access (acc $ size x)
  where
    acc : (sizeX : Nat) -> (y : a) -> (size y `LT` sizeX) -> SizeAccessible y
    acc (S x') y (LTESucc yLEx')
        = Access $ \z, zLTy => acc x' z $ transitive zLTy yLEx'

||| Depedently-typed induction based on the size of values.
|||
||| This is `accInd` applied to accessibility derived from size.
export
sizeInd : Sized a => {0 P : a -> Type} ->
          (step : (x : a) -> ((y : a) -> Smaller y x -> P y) -> P x) ->
          (z : a) ->
          P z
sizeInd step z = accInd step z (sizeAccessible z)

||| Simply-typed recursion based on the size of values.
|||
||| This is `recInd` applied to accessibility derived from size.
export
sizeRec : Sized a =>
          (step : (x : a) -> ((y : a) -> Smaller y x -> b) -> b) ->
          (z : a) -> b
sizeRec step z = accRec step z (sizeAccessible z)

export
Sized Nat where
  size = id

export
WellFounded Nat LT where
  wellFounded = sizeAccessible

export
Sized (List a) where
  size = length

export
(Sized a, Sized b) => Sized (Pair a b) where
  size (x,y) = size x + size y
