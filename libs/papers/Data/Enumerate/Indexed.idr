||| The content of this module is based on the paper
||| A Completely Unique Account of Enumeration
||| by Cas van der Rest, and Wouter Swierstra
||| https://doi.org/10.1145/3547636

module Data.Enumerate.Indexed

import Data.List
import Data.Description.Regular
import Data.Description.Indexed

import Data.Enumerate.Common

%default total

------------------------------------------------------------------------------
-- Definition of indexed enumerators
------------------------------------------------------------------------------

||| An (a,b)-enumerator is an enumerator for values of type b provided
||| that we already know how to enumerate subterms of type a
export
record IEnumerator {i : Type} (a : i -> Type) (b : Type) where
  constructor MkIEnumerator
  runIEnumerator : ((v : i) -> List (a v)) -> List b

------------------------------------------------------------------------------
-- Combinators to build enumerators
------------------------------------------------------------------------------

export
Functor (IEnumerator a) where
  map f (MkIEnumerator enum) = MkIEnumerator (map f . enum)

export
Applicative (IEnumerator a) where
  pure = MkIEnumerator . const . pure
  MkIEnumerator e1 <*> MkIEnumerator e2
    = MkIEnumerator (\ as => prodWith ($) (e1 as) (e2 as))

export
Alternative (IEnumerator a) where
  empty = MkIEnumerator (const [])
  MkIEnumerator e1 <|> MkIEnumerator e2
    = MkIEnumerator (\ as => interleave (e1 as) (e2 as))

export
Monad (IEnumerator a) where
  xs >>= ks = MkIEnumerator $ \ as =>
    foldr (\ x => interleave (runIEnumerator (ks x) as)) []
      (runIEnumerator xs as)

export
rec : (v : i) -> IEnumerator a (a v)
rec v = MkIEnumerator ($ v)

export
pairWith : (b -> c -> d) -> IEnumerator a b -> IEnumerator a c -> IEnumerator a d
pairWith f (MkIEnumerator e1) (MkIEnumerator e2)
  = MkIEnumerator (\ as => prodWith f (e1 as) (e2 as))

export
pair : IEnumerator a b -> IEnumerator a c -> IEnumerator a (b, c)
pair = pairWith (,)

export
sig : {b : a -> Type} ->
      IEnumerator f a -> ((x : a) -> IEnumerator f (b x)) ->
      IEnumerator f (x : a ** b x)
sig as bs = as >>= \ a => bs a >>= \ b => pure (a ** b)

export
const : List b -> IEnumerator a b
const bs = MkIEnumerator (const bs)

------------------------------------------------------------------------------
-- Extracting values by running an enumerator
------------------------------------------------------------------------------

export
isized : ((v : i) -> IEnumerator a (a v)) -> Nat -> (v : i) -> List (a v)
isized f 0 v = []
isized f (S n) v = runIEnumerator (f v) (isized f n)

------------------------------------------------------------------------------
-- Defining  generic enumerators for indexed datatypes
------------------------------------------------------------------------------

export
indexed : (d : i -> IDesc List i) -> (v : i) -> IEnumerator (Fix d) (Fix d v)
indexed d v = MkFix <$> go (d v) where

  go : (e : IDesc List i) -> IEnumerator (Fix d) (Elem e (Fix d))
  go Zero = empty
  go One = pure ()
  go (Id v) = rec v
  go (d1 * d2) = pair (go d1) (go d2)
  go (d1 + d2) = Left <$> go d1 <|> Right <$> go d2
  go (Sig s vs f) = sig (const vs) (\ x => go (f x))

export
0 Memorator : (d : Desc p) -> (Fix d -> Type) -> Type -> Type
Memorator d a b = (d ~> (List . a)) -> List b

export
memorate : {d : Desc p} ->
           {0 b : Fix d -> Type} ->
           ((x : Fix d) -> Memorator d b (b x)) ->
           Nat -> (x : Fix d) -> List (b x)
memorate f 0 x = []
memorate f (S n) x = f x (trie $ memorate f n)
