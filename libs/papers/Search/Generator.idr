||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor
||| https://doi.org/10.1145/2976022.2976030
|||
||| The main difference is that we use `Colist1` for the type of
||| generators rather than `Stream`. This allows us to avoid generating
||| many duplicates when dealing with finite types which are common in
||| programming (Bool) but even more so in dependently typed programming
||| (Vect 0, Fin (S n), etc.).

module Search.Generator

import Data.Colist
import Data.Colist1
import Data.Fin
import Data.Stream
import Data.Vect

------------------------------------------------------------------------
-- Interface

||| A generator for a given type is a non-empty colist of values of that
||| type.
public export
interface Generator a where
  generate : Colist1 a

------------------------------------------------------------------------
-- Implementations

-- Finite types

||| ALL of the natural numbers
public export
Generator Nat where
  generate = fromStream nats

||| ALL of the booleans
public export
Generator Bool where
  generate = True ::: [False]

||| ALL of the Fins
public export
{n : Nat} -> Generator (Fin (S n)) where
  generate = fromList1 (allFins n)

-- Polymorphic generators

||| We typically want to generate a generator for a unit-terminated right-nested
||| product so we have this special case that keeps the generator minimal.
public export
Generator a => Generator (a, ()) where
  generate = map (,()) generate

||| Put two generators together by exploring the plane they define.
||| This uses Cantor's zig zag traversal
public export
(Generator a, Generator b) => Generator (a, b) where
  generate = plane generate (\ _ => generate)

||| Put two generators together by exploring the plane they define.
||| This uses Cantor's zig zag traversal
public export
{0 b : a -> Type} -> (Generator a, (x : a) -> Generator (b x)) =>
  Generator (x : a ** b x) where
  generate = plane generate (\ x => generate)

||| Build entire vectors of values
public export
{n : Nat} -> Generator a => Generator (Vect n a) where
  generate = case n of
    Z => [] ::: []
    S n => map (uncurry (::)) generate

||| Generate arbitrary lists of values
||| Departing from the paper, to avoid having infinitely many copies of
||| the empty list, we handle the case `n = 0` separately.
public export
Generator a => Generator (List a) where
  generate = [] ::: forget (planeWith listy generate vectors) where
    listy : (n : Nat) -> Vect (S n) a -> List a
    listy _ = toList

    vectors : (n : Nat) -> Colist1 (Vect (S n) a)
    vectors n = generate
