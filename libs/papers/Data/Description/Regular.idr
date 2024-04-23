||| The content of this module is based on the paper
||| A Completely Unique Account of Enumeration
||| by Cas van der Rest, and Wouter Swierstra
||| https://doi.org/10.1145/3547636

module Data.Description.Regular

%default total

||| Description of regular functors
||| @ p stores additional data for constant types
|||     e.g. the fact they are enumerable
public export
data Desc : (p : Type -> Type) -> Type where
  ||| The code for the empty type
  Zero : Desc p
  ||| The code for the unit type
  One : Desc p
  ||| The code for the identity functor
  Id : Desc p
  ||| The code for the constant functor
  Const : (0 s : Type) -> (prop : p s) -> Desc p
  ||| The code for the product of functors
  (*) : (d1, d2 : Desc p) -> Desc p
  ||| The code for the sum of functors
  (+) : (d1, d2 : Desc p) -> Desc p

||| Computing the meaning of a description as a functor
total public export
0 Elem : Desc p -> Type -> Type
Elem Zero x = Void
Elem One x = ()
Elem Id x = x
Elem (Const s _) x = s
Elem (d1 * d2) x = (Elem d1 x, Elem d2 x)
Elem (d1 + d2) x = Either (Elem d1 x) (Elem d2 x)

||| Elem does decode to functors
total export
map : (d : Desc p) -> (a -> b) -> Elem d a -> Elem d b
map d f = go d where

     go : (d : Desc p) -> Elem d a -> Elem d b
     go Zero v = v
     go One v = v
     go Id v = f v
     go (Const s _) v = v
     go (d1 * d2) (v, w) = (go d1 v, go d2 w)
     go (d1 + d2) (Left v) = Left (go d1 v)
     go (d1 + d2) (Right v) = Right (go d2 v)

||| A regular type is obtained by taking the fixpoint of
||| the decoding of a description.
||| Unfortunately Idris 2 does not currently detect that this definition
||| is total because we do not track positivity in function arguments
public export
data Fix : Desc p -> Type where
  MkFix : assert_total (Elem d (Fix d)) -> Fix d

namespace Example

  ListD : Type -> Desc (const ())
  ListD a = One + (Const a () * Id)

  RList : Type -> Type
  RList a = Fix (ListD a)

  Nil : RList a
  Nil = MkFix (Left ())

  (::) : a -> RList a -> RList a
  x :: xs = MkFix (Right (x, xs))

||| Fix is an initial algebra so we get the fold
total export
fold : {d : Desc p} -> (Elem d x -> x) -> Fix d -> x
fold alg (MkFix v) = alg (assert_total $ map d (fold alg) v)

||| Any function from a regular type can be memoised by building a memo trie
||| This build one layer of such a trie, provided we already know how to build
||| a trie for substructures.
total
0 Memo : (e : Desc p) -> ((a -> Type) -> Type) -> (Elem e a -> Type) -> Type
Memo Zero x b = ()
Memo One x b = b ()
Memo Id x b = x b
Memo (Const s prop) x b = (v : s) -> b v
Memo (d1 * d2) x b = Memo d1 x $ \ v1 => Memo d2 x $ \ v2 => b (v1, v2)
Memo (d1 + d2) x b = (Memo d1 x (b . Left), Memo d2 x (b . Right))

export infixr 0 ~>

||| A memo trie is a coinductive structure
export
record (~>) {p : Type -> Type} (d : Desc p) (b : Fix d -> Type) where
  constructor MkMemo
  getMemo : assert_total (Memo d (\ x => Inf (d ~> x)) (b . MkFix))

export
trie : {d : Desc p} -> {0 b : Fix d -> Type} -> ((x : Fix d) -> b x) -> d ~> b
trie f = MkMemo (go d (\ t => f (MkFix t))) where

  go : (e : Desc p) ->
       {0 b' : Elem e (Fix d) -> Type} ->
       (f : (x : Elem e (Fix d)) -> b' x) ->
       Memo e (\ x => Inf (d ~> x)) b'
  go Zero f = ()
  go One f = f ()
  go Id f = assert_total trie f
  go (Const s prop) f = f
  go (d1 * d2) f = go d1 $ \ v1 => go d2 $ \ v2 => f (v1, v2)
  go (d1 + d2) f = (go d1 (\ v => f (Left v)), go d2 (\ v => f (Right v)))

export
untrie : {d : Desc p} -> {0 b : Fix d -> Type} -> d ~> b -> ((x : Fix d) -> b x)
untrie (MkMemo f) (MkFix t) = go d f t where

  go : (e : Desc p) ->
       {0 b' : Elem e (Fix d) -> Type} ->
       Memo e (\ x => Inf (d ~> x)) b' ->
       (x : Elem e (Fix d)) -> b' x
  go Zero mem x = absurd x
  go One mem () = mem
  go Id mem x = untrie mem x
  go (Const s prop) mem x = mem x
  go (d1 * d2) mem (x, y) = go d2 (go d1 mem x) y
  go (d1 + d2) mem (Left x) = go d1 (fst mem) x
  go (d1 + d2) mem (Right x) = go d2 (snd mem) x

export
memo : {d : Desc p} -> (0 b : Fix d -> Type) ->
       ((x : Fix d) -> b x) -> ((x : Fix d) -> b x)
memo b f = untrie (trie f)
