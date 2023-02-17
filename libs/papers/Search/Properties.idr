||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor
||| https://doi.org/10.1145/2976022.2976030

module Search.Properties

import Data.Fuel
import Data.List.Lazy
import Data.List.Lazy.Quantifiers
import Data.Nat
import Data.So

import public Data.Stream
import public Data.Colist
import public Data.Colist1

import public Search.Negation
import public Search.HDecidable
import public Search.Generator

import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Type

||| Take the product of a list of types
public export
Product : List Type -> Type
Product = foldr Pair ()

||| A property amenable to testing
||| @cs is the list of generators we need (inferrable)
||| @a  is the type we hope is inhabited
||| NB: the longer the list of generators, the bigger the search space!
public export
record Prop (cs : List Type) (a : Type) where
  constructor MkProp
  ||| The function trying to find an `a` provided generators for `cs`.
  ||| Made total by consuming some fuel along the way.
  runProp : Colist1 (Product cs) -> Fuel -> HDec a

------------------------------------------------------------------------
-- Prop-like structure

||| A type constructor satisfying the AProp interface is morally a Prop
||| It may not make use of all of the powers granted by Prop, hence the
||| associated `Constraints` list of types.
public export
interface AProp (0 t : Type -> Type) where
  0 Constraints : List Type
  toProp : t a -> Prop Constraints a

||| Props are trivially AProp
public export
AProp (Prop cs) where
  Constraints = cs
  toProp = id

||| Half deciders are AProps that do not need any constraints to be satisfied
public export
AProp HDec where
  Constraints = []
  toProp = MkProp . const . const

||| Deciders are AProps that do not need any constraints to be satisfied
public export
AProp Dec where
  Constraints = []
  toProp = MkProp . (const . const . toHDec)

||| We can run an AProp to try to generate a value of type a
public export
check : (gen : Generator (Product cs)) => (f : Fuel) -> (p : Prop cs a) ->
        {auto pr : So (isTrue (runProp p (generate @{gen}) f))} -> a
check @{gen} f p @{pr} = evidence (runProp p (generate @{gen}) f) pr

||| Provided that we know how to generate candidates of type `a`, we can look
||| for a witness satisfying a given predicate over `a`.
public export
exists : {0 p : a -> Type} -> (aPropt : AProp t) =>
         ((x : a) -> t (p x)) ->
         Prop (a :: Constraints @{aPropt}) (DPair a p)
exists test = MkProp $ \ acs, fuel =>
  let candidates : LazyList a = take fuel (map fst acs) in
  let cs = map snd acs in
  let find = any candidates (\ x => runProp (toProp (test x)) cs fuel) in
  map toDPair find

------------------------------------------------------------------------
-- Examples

namespace GT11

  example : Prop ? (DPair Nat (\ i => Not (i `LTE` 10)))
  example = exists (\ i => not (isLTE 11 i))

  lemma : DPair Nat (\ i => Not (i `LTE` 10))
  lemma = check (limit 1000) example

namespace Pythagoras

  formula : Type
  formula = DPair Nat $ \ m =>
            DPair Nat $ \ n =>
            DPair Nat $ \ p =>
            (0 `LT` m, 0 `LT` n, 0 `LT` p
            , (m * m + n * n) === (p * p))

  search : Prop ? Pythagoras.formula
  search = exists $ \ m =>
           exists $ \ n =>
           exists $ \ p =>
           (isLT 0 m && isLT 0 n && isLT 0 p
           && decEq (m * m + n * n) (p * p))

  -- This one is quite a bit slower so it's better to run
  -- the compiled version instead
  lemma : HDec Pythagoras.formula
  lemma = runProp search generate (limit 10)
