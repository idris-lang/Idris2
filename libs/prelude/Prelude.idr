module Prelude

{-
The Prelude is minimal (since it is effectively part of the language
specification, this seems to be desirable - we should, nevertheless, aim to
provide a good selection of base libraries). A rule of thumb is that it should
contain the basic functions required by almost any non-trivial program.

As such, it should contain:

- Anything the elaborator can desugar to (e.g. pairs, unit, =, laziness)
- Basic types Bool, Nat, List, Dec, Maybe, Either
- The most important utility functions: id, the, composition, etc
- Interfaces for arithmetic and implementations for the primitives and
  basic types
- Char and String manipulation
- Show, Eq, Ord, and implementations for all types in the prelude
- Interfaces and functions for basic proof (cong, Uninhabited, etc) --
- Semigroup, Monoid
- Functor, Applicative, Monad and related functions
- Foldable, Traversable
- Range for range syntax
- Console IO and interfaces for supporting IO

Everything else should be in the base libraries, and imported as required.
In particular, proofs of Nat/List properties that almost never get used in
practice would probably be better in base libraries.

Everything should be total, unless there's a good justification for it not
to be (division by zero, as a concrete example).

(These guidelines will probably get revised a few times.)
-}

import public Builtin
import public PrimIO
import public Prelude.Basics as Prelude
import public Prelude.Cast as Prelude
import public Prelude.EqOrd as Prelude
import public Prelude.Interfaces as Prelude
import public Prelude.Interpolation as Prelude
import public Prelude.IO as Prelude
import public Prelude.Num as Prelude
import public Prelude.Ops as Prelude
import public Prelude.Show as Prelude
import public Prelude.Types as Prelude
import public Prelude.Uninhabited as Prelude
