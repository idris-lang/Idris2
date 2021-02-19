||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor

module Search.Generator

import Data.Stream

------------------------------------------------------------------------
-- Interface

||| A generator for a given type is a stream of values of that type
public export
interface Generator a where
  generate : Stream a

------------------------------------------------------------------------
-- Implementations

public export
Generator Nat where
  generate = nats

||| We typically want to generate a generator for a unit-terminated right-nested
||| product so we have this special case that keeps the generator minimal.
public export
Generator a => Generator (a, ()) where
  generate = map (,()) generate

||| Otherwise we can put two generators together by exploring the plane they
||| define by using Cantor's zig zag traversal
public export
(Generator a, Generator b) => Generator (a, b) where
  generate = plane generate generate
