||| The content of this module is based on the paper
||| A Completely Unique Account of Enumeration
||| by Cas van der Rest, and Wouter Swierstra
||| https://doi.org/10.1145/3547636

module Data.Enumerate

import Data.List
import Data.Description.Regular
import Data.Stream

import Data.Enumerate.Common

%default total

------------------------------------------------------------------------------
-- Definition of enumerators
------------------------------------------------------------------------------

||| An (a,b)-enumerator is an enumerator for values of type b provided
||| that we already know how to enumerate subterms of type a
export
record Enumerator (a, b : Type) where
  constructor MkEnumerator
  runEnumerator : List a -> List b

------------------------------------------------------------------------------
-- Combinators to build enumerators
------------------------------------------------------------------------------

export
Functor (Enumerator a) where
  map f (MkEnumerator enum) = MkEnumerator (\ as => f <$> enum as)

||| This interleaving is fair, unlike one defined using concatMap.
||| Cf. paper for definition of fairness
export
pairWith : (b -> c -> d) -> Enumerator a b -> Enumerator a c -> Enumerator a d
pairWith f (MkEnumerator e1) (MkEnumerator e2)
  = MkEnumerator (\ as => prodWith f (e1 as) (e2 as)) where

export
pair : Enumerator a b -> Enumerator a c -> Enumerator a (b, c)
pair = pairWith (,)

export
Applicative (Enumerator a) where
  pure = MkEnumerator . const . pure
  (<*>) = pairWith ($)

export
Monad (Enumerator a) where
  xs >>= ks = MkEnumerator $ \ as =>
    foldr (\ x => interleave (runEnumerator (ks x) as)) []
      (runEnumerator xs as)

export
Alternative (Enumerator a) where
  empty = MkEnumerator (const [])
  MkEnumerator e1 <|> MkEnumerator e2 = MkEnumerator (\ as => interleave (e1 as) (e2 as))

||| Like `pure` but returns more than one result
export
const : List b -> Enumerator a b
const = MkEnumerator . const

||| The construction of recursive substructures is memoised by
||| simply passing the result of the recursive call
export
rec : Enumerator a a
rec = MkEnumerator id

namespace Example

  data Tree : Type where
    Leaf : Tree
    Node : Tree -> Tree -> Tree

  tree : Enumerator Tree Tree
  tree = pure Leaf <|> Node <$> rec <*> rec

------------------------------------------------------------------------------
-- Extracting values by running an enumerator
------------------------------------------------------------------------------

||| Assuming that the enumerator is building one layer of term,
||| sized e n will produce a list of values of depth n
export
sized : Enumerator a a -> Nat -> List a
sized (MkEnumerator enum) = go where

  go : Nat -> List a
  go Z = []
  go (S n) = enum (go n)

||| Assuming that the enumerator is building one layer of term,
||| stream e will produce a list of increasingly deep values
export
stream : Enumerator a a -> Stream (List a)
stream (MkEnumerator enum) = iterate enum []

------------------------------------------------------------------------------
-- Defining generic enumerators for regular types
------------------------------------------------------------------------------

export
regular : (d : Desc List) -> Enumerator (Fix d) (Fix d)
regular d = MkFix <$> go d where

  go : (e : Desc List) -> Enumerator (Fix d) (Elem e (Fix d))
  go Zero = empty
  go One = pure ()
  go Id = rec
  go (Const s prop) = const prop
  go (d1 * d2) = pair (go d1) (go d2)
  go (d1 + d2) = Left <$> go d1 <|> Right <$> go d2

namespace Example

  ListD : List a -> Desc List
  ListD as = One + (Const a as * Id)

  lists : (xs : List a) -> Nat -> List (Fix (ListD xs))
  lists xs = sized (regular (ListD xs))

  encode : {0 xs : List a} -> List a -> Fix (ListD xs)
  encode = foldr (\x, xs => MkFix (Right (x, xs))) (MkFix (Left ()))

  decode : {xs : List a} -> Fix (ListD xs) -> List a
  decode = fold (either (const []) (uncurry (::)))

  -- [[], ['a'], ['a', 'a'], ['b'], ['a', 'b'], ['b', 'a'], ['b', 'b']]
  abs : List (List Char)
  abs = decode <$> lists ['a', 'b'] 3
