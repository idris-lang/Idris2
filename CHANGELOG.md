# Changelog

## [Next version]

### Language changes

* New magic constants `__LOC__`, `__FILE__`, `__LINE__`, `__COL__`
  substituted at parsing time with a string corresponding to the
  location, filename, line or column number associated to the
  magic constant's position.
* The termination checker is now a faithful implementation of the 2001 paper on
  size-change termination by Lee, Jones and Ben-Amram.
* New function option `%unsafe` to mark definitions that are escape hatches
  similar to the builtins `believe_me`, `assert_total`, etc.
* Elaborator scripts were made be able to record warnings.
* Rudimentary support for defining lazy functions (addressing issue
  [#1066](https://github.com/idris-lang/idris2/issues/1066)).
* `%hide` directives can now hide conflicting fixities from other modules.
* Fixity declarations can now be kept private with export modifiers.
* Forward-declarations whose visibility differ from their
  actual definition now emit a warning, unless the definition
  has no specified visibility
  (addressing Issue [#1236](https://github.com/idris-lang/Idris2/issues/1236)).
* New `fromTTImp`, `fromName`, and `fromDecls` names for custom `TTImp`,
  `Name`, and `Decls` literals.
* Call to `%macro`-functions do not require the `ElabReflection` extension.
* Default implicits are supported for named implementations.
* Elaborator scripts were made to be able to access project files,
  allowing the support for type providers and similar stuff.
* Elaborator scripts were made to be able to inspect which definitions are
  referred to by another definitions, and in which function currently elaborator is.
  These features together give an ability to inspect whether particular expressions
  are recursive (including mutual recursion).

### REPL changes

* Adds documentation for unquotes `~( )`.
* Adds documentation for laziness and codata primitives: `Lazy`, `Inf`, `Delay`,
  and `Force`.

### Backend changes

#### RefC

* Adds support for `CFLAGS`, `CPPFLAGS`, and `LDFLAGS` to facilitate building on
  systems with non-standard installation locations of libraries (e.g. GMP).
  Versions of the flags with the `IDRIS2_` prefix can also be used and take
  precedence.

#### Chez

* Non-recursive top-level constants are compiled to eagerly evaluated
  constants in Chez Scheme.

#### Racket

* FFI declarations can now specify which `require` to perform, i.e. which
  library to load before executing the FFI.
  The syntax is `scheme,racket:my-function,my-library`.

#### Node.js/Browser

* Generated JavaScript files now include a shebang when using the Node.js backend
* NodeJS now supports `popen`/`pclose` for the `Read` mode.
* `getChar` is now supported on Node.js and `putChar` is supported on both
  JavaScript backends.
* Integer-indexed arrays are now supported.

### Compiler changes

* If `IAlternative` expression with `FirstSuccess` rule fails to typecheck,
  compiler now prints all tried alternatives, not only the last one.

* The elaboration of records has been changed so that the unbound implicits in
  the parameters' types become additional parameters e.g.
  ```idris2
  record HasLength (xs : List a) (n : Nat) where
    constructor MkHasLength
    0 prf : length xs === n
  ```
  is now correctly elaborated to
  ```idris2
  record HasLength {0 a : Type} (xs : List a) (n : Nat) where
    constructor MkHasLength
    0 prf : length xs === n
  ```
  instead of failing with a strange error about (a) vs (a .rec).

* Elaboration of datatypes now respects the totality annotations:
  defining a `covering` or `partial` datatype in a `%default total`
  file will not lead to a positivity error anymore.

* Fixed a bug in the positivity checker that meant `Lazy` could be used
  to hide negative occurrences.

* Made sure that the positivity checker now respects `assert_total` annotations.

* We now raise a warning for conflicting fixity declarations. They are
  dangerous as Idris will pick an arbitrary one and so the meaning of an
  expression can depend e.g. on the order in which modules are imported.

  * Additionally some conflicting fixity declarations in the Idris 2 compiler
    and libraries have been removed.

* Constructors mentioned on the left hand side of functions/case alternatives
  are now included in the `Refers to (runtime)` section of functions debug info.

* The Lifted IR Representation now has a `HasNamespaces` implementation
  in `Compiler.Separate` so Compilation Units at that stage can be generated.

* Added the `compile.casetree.missing` log topic, along with its use in
  `TTImp.ProcessDef.genRunTime`. This allows us to track when incomplete `case`
  blocks get the runtime error added.

* Constant folding of trivial let statements and `believe_me`.

* Fixed a bug that caused holes to appear unexpectedly during quotation of
  dependent pairs.

* Fixed a bug that caused `f` to sometimes be replaced by `fx` after matching `fx = f x`.

* Fixed a bug in the totality checker that missed indirect references to
  partial data.

* Refactor the idris2protocols package to depend on fewer Idris2 modules.
  We can now export the package independently.
  To avoid confusing tooling about which `.ipkg` to use, the
  package file is under the newly added `ipkg` sub-directory.

* Added `Libraries.Data.WithDefault` to facilitate consistent use
  of a default-if-unspecified value, currently for `private` visibility.

### Library changes

#### Prelude

* Improved performance of functions `isNL`, `isSpace`, and `isHexDigit`.

* Implements `Foldable` and `Traversable` for pairs, right-biased as `Functor`.

* Added a constructor (`MkInterpolation`) to `Interpolation`.

* Added an `Interpolation` implementation for `Void`.

* Added `Compose` instances for `Bifunctor`, `Bifoldable` and `Bitraversable`.

#### Base

* Deprecates `setByte` and `getByte` from `Data.Buffer` for removal in a future
  release. Use `setBits8` and `getBits8` instead (with `cast` if you need to
  convert a `Bits8` to an `Int`), as their values are limited, as opposed to the
  assumption in `setByte` that the value is between 0 and 255.

* Adds RefC support for 16- and 32-bit access in `Data.Buffer`.
* Add `Show` instance to `Data.Vect.Quantifiers.All` and add a few helpers for listy
  computations on the `All` type.
* Add an alias for `HVect` to `All id` in `Data.Vect.Quantifiers.All`. This is the
  approach to getting a heterogeneous `Vect` of elements that is general
  preferred by the community vs. a standalone type as seen in `contrib`.
* Add `Data.List.HasLength` from the compiler codebase slash contrib library but
  adopt the type signature from the compiler codebase and some of the naming
  from the contrib library. The type ended up being `HasLength n xs` rather than
  `HasLength xs n`.

* `System`'s `die` now prints the error message on stderr rather than stdout

* Moved `Data.SortedMap` and `Data.SortedSet` from contrib to base.

* Added missing buffer primitives (chezscheme only):
  `setInt8`, `getInt8`, `getInt16`, `setInt64`, `getInt64`

* Added new buffer (set/get) functions for built-in types `Bool`, `Nat`, `Integer`.

* Tightened the types of:
  `setInt16` (now takes an `Int16` instead of an `Int`),
  `setInt32` (now takes an `Int32` instead of an `Int`),
  `getInt32` (now returns an `Int32` instead of an `Int`)

* Adds left- and right-rotation for `FiniteBits`.

* Adds `Vect.permute` for applying permutations to `Vect`s.
* Adds `Vect.kSplits` and `Vect.nSplits` for splitting a `Vect` whose length is
  a known multiple of two `Nat`s (k * n) into k vectors of length n (and
  vice-versa).
* Adds `Vect.allFins` for generating all the `Fin` elements as a `Vect` with
  matching length to the number of elements.

* Add `withRawMode`, `enableRawMode`, `resetRawMode` for character at a time
  input on stdin.

* Adds extraction functions to `Data.Singleton`.

* `TTImp` reflection functions are now `public export`, enabling use at the
  type-level.

* Implemented `Eq`, `Ord`, `Semigroup`, and `Monoid` for `Data.List.Quantifiers.All.All`
  and `Data.Vect.Quantifiers.All.All`.

* Generalized `imapProperty` in `Data.List.Quantifiers.All.All`
  and `Data.Vect.Quantifiers.All.All`.

* Add `zipPropertyWith`, `traverseProperty`, `traversePropertyRelevant` and `remember`
  to `Data.Vect.Quantifiers.All.All`.

* Add `anyToFin` to `Data.Vect.Quantifiers.Any`,
  converting the `Any` witness to the index into the corresponding element.

* Implemented `Ord` for `Language.Reflection.TT.Name`, `Language.Reflection.TT.Namespace`
  and `Language.Reflection.TT.UserName`.

* Adds `leftmost` and `rightmost` to `Control.Order`, a generalisation of `min` and `max`.

* Adds `even` and `odd` to `Data.Integral`.
* `Eq` and `Ord` implementations for `Fin n` now run in constant time.

* Adds `getTermCols` and `getTermLines` to the base library. They return the
  size of the terminal if either stdin or stdout is a tty.

* The `Data.List1` functions `foldr1` and `foldr1By` are now `public export`.

* Added `uncons' : List a -> Maybe (a, List a)` to `base`.

* Adds `infixOfBy` and `isInfixOfBy` into `Data.List`.

* Adds `WithDefault` into `Language.Reflection.TTImp`, mirroring compiler addition.

* Adds updating functions to `SortedMap` and `SortedDMap`.

* Adds `grouped` function to `Data.List` for splitting a list into equal-sized slices.

* Implements `Ord` for `Count` from `Language.Reflection`.

* Implements `MonadState` for `Data.Ref` with a named implementation requiring
  a particular reference.

* Adds implementations of `Zippable` to `Either`, `Pair`, `Maybe`, `SortedMap`.

* Adds a `Compose` and `FromApplicative` named implementations for `Zippable`.

* Adds `Semigroup`, `Applicative`, `Traversable` and `Zippable` for `Data.These`.

* Adds bindings for IEEE floating point constants NaN and (+/-) Inf, as well as
  machine epsilon and unit roundoff. Speeds vary depending on backend.

* A more generalised way of applicative mapping of `TTImp` expression was added,
  called `mapATTImp`; the original `mapMTTimp` was implemented through the new one.

#### System

* Changes `getNProcessors` to return the number of online processors rather than
  the number of configured processors.

* Adds `popen2` to run a subprocess with bi-directional pipes.

### Contrib

* Adds `Data.List.Sufficient`, a small library defining a structurally inductive
  view of lists.

* Remove `Data.List.HasLength` from `contrib` library but add it to the `base`
  library with the type signature from the compiler codebase and some of the
  naming from the `contrib` library. The type ended up being `HasLength n xs`
  rather than `HasLength xs n`.

* Adds an implementation for `Functor Text.Lexer.Tokenizer.Tokenizer`.

* Adds `modFin` and `strengthenMod` to `Data.Fin.Extra`. These functions reason
  about the modulo operator's upper bound, which can be useful when working with
  indices (for example).

* Existing specialised variants of functions from the `Traversable` for `LazyList`
  were made to be indeed lazy by the effect, but their requirements were strengthened
  from `Applicative` to `Monad`.

* Implements `Sized` for `Data.Seq.Sized` and `Data.Seq.Unsized`.

#### Papers

* In `Control.DivideAndConquer`: a port of the paper
  "A Type-Based Approach to Divide-And-Conquer Recursion in Coq"
  by Pedro Abreu, Benjamin Delaware, Alex Hubers, Christa Jenkins,
  J. Garret Morris, and Aaron Stump.
  [https://doi.org/10.1145/3571196](https://doi.org/10.1145/3571196)

* Ports the first half of "Deferring the Details and Deriving Programs" by Liam
  O'Connor as `Data.ProofDelay`.
  [https://doi.org/10.1145/3331554.3342605](https://doi.org/10.1145/3331554.3342605)
  [http://liamoc.net/images/deferring.pdf](http://liamoc.net/images/deferring.pdf)

### Other Changes

* The `data` subfolder of an installed or local dependency package is now automatically
  recognized as a "data" directory by Idris 2. See the
  [documentation on Packages](https://idris2.readthedocs.io/en/latest/reference/packages.html)
  for details.
* The compiler no longer installs its own C support library into
  `${PREFIX}/lib`. This folder's contents were always duplicates of files
  installed into `${PREFIX}/idris2-${IDRIS2_VERSION}/lib`. If you need to adjust
  any tooling or scripts, point them to the latter location which still contains
  these installed library files.
* Renamed `support-clean` Makefile target to `clean-support`. This is in line
  with most of the `install-<something>` and `clean-<something>` naming.
* Fixes an error in the `Makefile` where setting `IDRIS2_PREFIX` caused
  bootstrapping to fail.
* Updates the docs for `envvars` to match the changes introduced in #2649.
* Both `make install` and `idris2 --install...` now respect `DESTDIR` which
  can be set to install into a staging directory for distro packaging.
* Updates the docs for `envvars` to categorise when environment variables are
  used (runtime, build-time, or both).
* Fixed build failure occuring when `make -j` is in effect.

## v0.6.0

### REPL changes

* New experimental Scheme based evaluator (only available if compiled via
  Chez scheme or Racket). To access this at the REPL, set the evaluator mode to
  the scheme based evaluator with `:set eval scheme`.
* New option `evaltiming` to time how long an evaluation takes at the REPL,
  set with `:set evaltiming`.
* Renames `:lp/loadpackage` to `:package`.
* Adds `:import`, with the same functionality as `:module`.
* Adds the ability to request detailed help via `:help <replCmd>`, e.g.
  `:help :help` or `:help :let`. This also works with the `:?` and `:h` aliases.

### Language changes

* There were two versions of record syntax used when updating records:

  ```idris
  record { field = value } r
  ```

  and

  ```idris
  { field := value } r
  ```

  The former is now deprecated in favour of the latter syntax.
  The compiler will issue a warning when using the `record` keyword.

* Interpolated strings now make use of `concat` which is compiled into
  `fastConcat`.
  The interpolated slices now make use of the `Interpolation` interface
  available in the prelude. It has only one method `interpolate` which is called
  for every expression that appears within an interpolation slice.

  ```idris
  "hello \{world}"
  ```

  is desugared into

  ```idris
  concat [interpolate "hello ", interpolate world]
  ```

  This allows you to write expressions within slices without having to call
  `show` but for this you need to implement the `Interpolation` interface for
  each type that you intend to use within an interpolation slice. The reason for
  not reusing `Show` is that `Interpolation` and `Show` have conflicting
  semantics, typically this is the case for `String` which adds double quotes
  around the string.

* Adds a `failing` block that requires its body to fail with a compile error.
  Optionally this block may contain a string which is checked to be contained in
  the error message.

* Bodies of `mutual`, `failing`, `using` and `parameters` blocks are required to
  be indented comparing to the position of the keyword.

* `%nomangle` has been deprecated in favour of `%export`.

* Records now support DataOpts, i.e. we can write things like
  ```idris
  record Wrap (phantom : Type) (a : Type) where
    [search a]    -- this was previously not supported
    constructor MkWrap
    unWrap : a
  ```

* Adds ability to forward-declare interface implementations, e.g.:
  ```idris
  implementation IsOdd Nat    -- forward declare for use in `IsEven`

  implementation IsEven Nat where
   isEven 0 = True
   isEven (S k) = not $ isOdd k

  implementation IsOdd Nat where
    isOdd 0 = False
    isOdd (S k) = not $ isEven k
  ```

* Adds ability to forward-declare records, e.g.:
  ```idris
  record B
  record A where
    b : B
  record B where
    a : A
  ```

### Compiler changes

* Removes deprecated support for `void` primitive. Now `void` is supported via
  `prim__void`.
* Adds `%deprecate` pragma that can be used to warn when deprecated functions
  are used.
* Package files now support a `langversion` field that can be used to specify
  what versions of Idris a package supports. As with dependency versions, `>`,
  `<`, `>=`, and `<=` can all be used.
  + For example, `langversion >= 0.5.1`.
* Alternatives for primitive types of the `Core.TT.Constant` are moved out to a
  separate data type `PrimTypes`. Signatures of functions that were working with
  `Constant` are changed to use `PrimTypes` when appropriate.
* Codegens now take an additional `Ref Syn SyntaxInfo` argument. This empowers
  compiler writers to pretty print core terms e.g. to add comments with the
  original type annotations in the generated code.
* `Refc.showcCleanStringChar` forgot some symbols which have now been added,
  ensuring the string is properly cleaned.
* Constant-folds all casts and integral expressions (with the exception of type
  `Int`), leading to improved performance.
* Increases accuracy of error reporting for keywords.
* Adds the `eval.stuck.outofscope` log topic in order to be able to spot when we
  get stuck due to a function being out of scope.
* Improves the error reporting for syntactically incorrect records.
* `IPragma` now carries an `FC` with it for better error reporting.
* Adds the number of enum constructors to enum types during codegen, to allow
  for trivial conversion to, e.g., `Bits32`.
* Adds constant-folding for `Nat` literals.
* Fixes `CyclicMeta` in `TTImp.ProcessDef` being considered a recoverable error.


### IDE protocol changes

* The IDE protocol and its serialisation to S-Expressions are factored
  into a separate module hierarchy Protocol.{Hex, SExp, IDE}.

* File context ranges sent in the IDE protocol follow the same
  convention as Bounds values in the parser:
  + all offsets (line and column) are 0-based.
  + Lines: start and end are within the bounds
  + Column:
    + start column is within the bounds;
    + end   column is after the bounds.

  This changes behaviour from previous versions of the protocol.
  Matching PRs in the emacs modes:
  + idris2-mode [PR#11](https://github.com/idris-community/idris2-mode/pull/11)
  + idris-mode [PR#547](https://github.com/idris-hackers/idris-mode/pull/547)

* The IDE protocol now supports specifying a socket and hostname via the
    `--ide-mode-socket` flag, allowing multiple IDE server instances to run on
    the same machine.

### Interactive Editing changes

* Case-split no longer generates syntactically invalid Idris when splitting on
  auto-implicits.
* Case-split no longer shadows the function name when an internal named argument
  has the same name as the function.
* Case-split now avoids using upper-case names for pattern variables.

### Library changes

#### Prelude

* `elemBy` and `elem` are now defined for any `Foldable` structure. The
  specialised versions defined in `Data.(List/SnocList/Vect)` have been removed.
* `filter` and `mapMaybe` functions for `List` were moved to `prelude` from
  `base`.
* Basic functions of `SnocList` (`(++)`, `length`, `filter`, `mapMaybe`) and
  implementations of `Eq` and `Ord` were moved to `prelude` from `base`.
  This may lead to a need to qualifying functions (e.g. `List.filter`) due to
  possible ambiguity.
* "Fish" and "chips" operators of `SnocList` were moved to `Prelude.Types` from
  `Prelude.Basics`.
* Adds `contra` for returning the opposite of a given `Ordering`.
* Fix `pow`, using backend implementations.
* Add `subtract` alias for `(-)`

#### Base

* Adds `System.run`, which runs a shell command, and returns the stdout and
  return code of that run.
* Adds escaped versions of `System.system`, `Systen.File.popen`, and
  `System.run`, which take a list of arguments, and escapes them.
* Adds the `Injective` interface in module `Control.Function`.
* Changes `System.pclose` to return the return code of the closed process.
* Deprecates `base`'s `Data.Nat.Order.decideLTE` in favor of `Data.Nat.isLTE`.
* Removes `base`'s deprecated `System.Directory.dirEntry`. Use `nextDirEntry`
  instead.
* Removes `base`'s deprecated `Data.String.fastAppend`. Use `fastConcat`
  instead.
* `System.File.Buffer.writeBufferData` now returns the number of bytes that have
  been written when there is a write error.
* `System.File.Buffer.readBufferData` now returns the number of bytes that have
  been read into the buffer.
* Adds the `Data.List.Quantifiers.Interleaving` and
  `Data.List.Quantifiers.Split` datatypes, used for provably splitting a list
  into a list of proofs and a list of counter-proofs for a given property.
* Properties of the `List1` type were moved from `Data.List1` to
  `Data.List1.Properties`.
* `Syntax.PreorderReasoning` was moved to `base` from `contrib`.
* Move the types and functions in `Data.Vect.Quantifiers` to their respective
  namespaces (`All` for all-related things, and `Any` for any-related things) to
  make the code consistent with the other quantifiers (`List` and `SnocList`).
* Set the `all` and `any` functions for proof-quantifiers to `public export`
  instead of `export`, allowing them to be used with auto-implicit `IsYes`.
* Legacy duplicating type `Given` (with constructor `Always`) is removed from
  the `Decidable.Decidable`. Use the type `IsYes` (with constructor `ItIsYes`)
  from the same module instead.
* Adds `Data.List1.Elem`, ported from `Data.List.Elem`.
* Adds `Data.List1.Quantifiers`, ported from `Data.List.Quantifiers`.
* Changes the order of arguments in `RWST` transformer's runners functions
  (`runRWST`. `evalRWST`, `execRWST`), now transformer argument is the last, as
  in the other standard transformers, like `ReaderT` and `StateT`.
* Adds `Data.Fin.finToNatEqualityAsPointwise`,
  which takes a witness of `finToNat k = finToNat l` and proves `k ~~~ l`.
* Drop first argument (path to the `node` executable) from `System.getArgs` on
  the Node.js backend to make it consistent with other backends.
* Adds `Uninhabited` instances for `FZ ~~~ FS k` and `FS k ~~~ FZ`.
* Change behavior of `channelPut` on the Racket backend to match the behavior
  on the Chez backend.
* `fGetLine` has been marked as `covering` instead of `total`.
* Adds the ability to derive `Functor` and `Traversable` using `%runElab derive`
    in the implementation definition.
* Fixes memory leaks in `currentDir`, `fGetLine`, and `fGetChars`.
* Fixes `natToFinLT` being O(n) by proving that `So (x < n)` implies `LT x n`,
    allowing the compiler to optimise `natToFinLT` away.
* Fixes `SnocList.foldr` and `SnocList.foldMap` to be performant and stack-safe.
* Add `insertAt`, `deleteAt` and `replaceAt` for `List`
* Add `scanr`, `scanr1` and `unsnoc` for `Vect`
* Implement `DecEq` for `SnocList`

#### Test

* Refactors `Test.Golden.runTest` to use `System.Concurrency` from the base
  libraries instead of `System.Future` from `contrib`. In addition to reducing
  the dependency on `contrib` in the core of Idris2, this also seems to provide
  a small performance improvement for `make test`.
* Splits `runner` into `runnerWith` for processing the options and configuring
  the test pools, and a new `runner` function for reading options from the
  command-line.

#### Contrib

* `System.Random` support for `Int` changed to `Int32`; it already limited
  itself to 32 bits but now that is codified. JavaScript backends are now
  supported.
* Removes `contrib`'s deprecated `Data.Num.Implementations` module. See
  `Prelude.Interfaces` instead.
* Implements `Show tok => Show (ParsingError tok)` for `Text.Parser.Core`.
* `Control.Linear.LIO` has been moved from `contribs` to `linear` to guarantee
  that idris2 does not need to rely on contribs anymore.

#### Network

* `Control.Linear.Network` now supports `connect` in the linear environment, and
  can also access the `sendBytes`, `recvBytes` and `recvAllBytes` functions of
  the underlying `Socket` module.

#### Papers, Linear

* Creates the `papers` and `linear` libraries to remove bits of type theory and
  pl propaganda from `contrib` and instead clearly have them as implementations
  of their respective papers.
* Creates `Data.Linear.{Notation,LEither,LMaybe,LVect,Pow}`.

* Moves `Data.Container`, based on the papers "Categories of Containers" by
  Michael Abbott, Thorsten Altenkirch, and Neil Ghani, and "Derivatives of
  Containers" by Michael Abbott, Thorsten Altenkirch, Neil Ghani, and Conor
  McBride, to `papers`.
  [https://doi.org/10.1007/3-540-36576-1_2](https://doi.org/10.1007/3-540-36576-1_2)
  [https://doi.org/10.1007/3-540-44904-3_2](https://doi.org/10.1007/3-540-44904-3_2)
* Moves the implementation of "Indexed induction-recursion" by Dybjer and Setzer
  to `papers`.
  [https://doi.org/10.1016/j.jlap.2005.07.001](https://doi.org/10.1016/j.jlap.2005.07.001)
* Ports "How to Take the Inverse of a Type" by Daniel Marshall and Dominic
  Orchard as `Data.Linear.{Communications,Diff,Inverse}`.
  [https://doi.org/10.4230/LIPIcs.ECOOP.2022.5](https://doi.org/10.4230/LIPIcs.ECOOP.2022.5)
* Moves `Data.OpenUnion`, inspired by the paper "Freer monads, more extensible
  effects" by Oleg Kiselyov and Hiromi Ishii, to `papers`.
  [https://doi.org/10.1145/2887747.2804319](https://doi.org/10.1145/2887747.2804319)
* Moves `Data.Recursion.Free`, partially based on "Turing-Completeness Totally
  Free" by Conor McBride, to `papers`.
  [https://doi.org/10.1007/978-3-319-19797-5_13](https://doi.org/10.1007/978-3-319-19797-5_13)
* Moves `Data.Tree.Perfect` to `papers`.
* Moves `Data.Vect.Binary`, taken from the paper "Heterogeneous Binary
  Random-access Lists" by Wouter Swierstra, to `papers`.
  [https://doi.org/10.1017/S0956796820000064](https://doi.org/10.1017/S0956796820000064)
* Ports "Applications of Applicative Proof Search" by Liam O'Connor as
  `Search.{Generator,HDecidable,Negation,Properties,CTL,GCL}`.
  [https://doi.org/10.1145/2976022.2976030](https://doi.org/10.1145/2976022.2976030)
* Implements "Dependent Tagless Final" by Nicolas Biri as `Language.Tagless`.
  [https://doi.org/10.1145/3498886.3502201](https://doi.org/10.1145/3498886.3502201)
* Ports Todd Waugh Ambridge's Agda blog post series "Search over uniformly
  continuous decidable predicates on infinite collections of types" as
  `Search.Tychonoff`.
  [https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html](https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html)
* Ports "Auto in Agda - Programming proof search using reflection" by Wen Kokke
  and Wouter Swierstra as `Search.Auto`.
  [https://doi.org/10.1007/978-3-319-19797-5_14](https://doi.org/10.1007/978-3-319-19797-5_14)
* Ports "Computing with Generic Trees in Agda" by Stephen Dolan as `Data.W`.
  [https://doi.org/10.1145/3546196.3550165](https://doi.org/10.1145/3546196.3550165)

### Other changes

* Adds docstrings for the lambda-lifted IR.
* Package files are now installed along-side build artifacts for installed
  packages. This means all transitive dependencies of packages you specify with
  the `depends` field are added automatically.
* No longer builds `contrib` and `papers` during bootstrap, as these may rely on
  new features not yet present in the bootstrap version of Idris2.

## v0.5.0/0.5.1

### Language changes

* Missing methods in implementations now give a compile time error. This was
  always the intended behaviour, but until now had not been implemented!
* Records now work in `parameters` blocks and `where` clauses.
* Implementations of interfaces now work in `parameters` blocks and
  `where` clauses
* The syntax for Name reflection has changed, and now requires a single brace
  instead of a double brace, e.g. `` `{x} ``
* Raw string literals allows writing string while customising the escape
  sequence. Start a string with `#"` in order to change the escape characters
  to `\#`, close the string with `"#`. Remains compatible with multiline
  string literals.
* Interpolated strings allows inserting expressions within string literals
  and avoid writing concatenation explicitly. Escape a left curly brace `\{`
  to start an interpolation slice and close it with a right curly brace `}` to
  resume writing the string literal. The enclosed expression must be of type
  `String`. Interpolated strings are compatible with raw strings (the slices
  need to be escaped with `\#{` instead) and multiline strings.
* We now support ellipses (written `_`) on the left hand side of a `with`
  clause. Ellipses are substituted for by the left hand side of the parent
  clause i.e.

```idris
  filter : (p : a -> Bool) -> List a -> List a
  filter p []        = []
  filter p (x :: xs) with (p x)
    _ | True  = x :: filter p xs
    _ | False = filter p xs
```

means

```idris
filter : (p : a -> Bool) -> List a -> List a
filter p []        = []
filter p (x :: xs) with (p x)
  filter p (x :: xs) | True  = x :: filter p xs
  filter p (x :: xs) | False = filter p xs
```



### Compiler changes

* Added incremental compilation, using either the `--inc` flag or the
  `IDRIS2_INC_CGS` environment variable, which compiles modules incrementally.
  In incremental mode, the final build step is much faster than in whole
  program mode (the default), at the cost of runtime performance being about
  half as good. The `--whole-program` flag overrides incremental compilation,
  and reverts to whole program compilation. Incremental compilation is currently
  supported only by the Chez Scheme back end.
  This is currently supported only on Unix-like platforms (not yet Windows)
  - Note that you must set `IDRIS2_INC_CGS` when building and installing
    all libraries you plan to link with an incremental build.
  - Note also that this is experimental and not yet well tested!
* The type checker now tries a lot harder to avoid reducing expressions where
  it is not needed. This can give a huge performance improvement in programs
  that potentially do a lot of compile time evaluation. However, sometimes
  reducing expressions can help in totality and quantity checking, so this may
  cause some programs not to type check which previously did - in these cases,
  you will need to give the reduced expressions explicitly.

### REPL/CLI/IDE mode changes

* Added `--list-packages` CLI option.
* Added `--total` CLI option.

### Library changes

#### Prelude

Changed

- Removed `Data.Strings`.  Use `Data.String` instead.

#### System.Concurrency

* Reimplement the `Channels` primitive in the Chez-Scheme backend since it had
  some non-deterministic properties (see issue
  [#1552](https://github.com/idris-lang/idris2/issues/1552)).
  NOTE: Due to complications with race-conditions, Chez not having channels
  built-in, etc, the reimplementation changes the semantics slightly:
  `channelPut` no longer blocks until the value has been received under the
  `chez` backend, but instead only blocks if there is already a value in the
  channel that has not been received.
  With thanks to Alain Zscheile (@zseri) for help with understanding condition
  variables, and figuring out where the problems were and how to solve them.

#### Control.Relation, Control.Order

* The old system of interfaces for defining order relations (to say,
  for instance, that LTE is a partial order) is replaced with a new
  system of interfaces. These interfaces defines properties of binary
  relations (functions of type `ty -> ty -> Type`), and orders are
  defined simply as bundles of these properties.

### Installation changes

* Added a new makefile target to install Idris 2 library documentation.  After `make install`, type
  `make install-libdocs` to install it.  After that, the index file can be found here: ``idris2
  --libdir`/docs/index.html`.``

## v0.4.0

### Syntax changes

* Desugar non-binding sequencing in do blocks to (`>>`)
  ([#1095](https://github.com/idris-lang/idris2/pull/1095))
* Multiline Strings with `"""` as delimiters
  ([#1097](https://github.com/idris-lang/idris2/pull/1097))
* Force strict indentation after usage of `with` keyword
  ([#1107](https://github.com/idris-lang/idris2/pull/1107))
* The syntax for parameter blocks has been updated. It now allows to declare
  implicit parameters and give multiplicities for parameters. The old syntax is
  still available for compatibility purposes but will be removed in the future.
* Add support for SnocList syntax: `[< 1, 2, 3]` desugars into `Lin :< 1 :< 2 :<
  3` and their semantic highlighting.
* Underscores can be used as visual separators for digit grouping purposes in
  integer literals: `10_000_000` is equivalent to `10000000` and
  `0b1111_0101_0000` is equivalent to `0b111101010000`. This can aid readability
  of long literals, or literals whose value should clearly separate into parts,
  such as bytes or words in hexadecimal notation.

### Compiler changes

* Added more optimisations and transformations, particularly on case blocks,
  list-shaped types, and enumerations, so generated code will often be slightly
  faster.
* Added `--profile` flag, which generates profile data if supported by a back
  end. Currently supported by the Chez and Racket backends.
* New `%builtin` pragma for compiling user defined natural numbers to primitive
  `Integer`s (see the
  [docs](https://idris2.readthedocs.io/en/latest/reference/builtins.html))
* The `version` field in `.ipkg` files is now used. Packages are installed into
  a directory which includes its version number, and dependencies can have
  version number ranges using `<=`, `<`, `>=`, `>`, `==` to express version
  constraints. Version numbers must be in the form of integers, separated by
  dots (e.g. `1.0`, `0.3.0`, `3.1.4.1.5` etc)
* Idris now looks in the current working directory, under a subdirectory
  `depends` for local installations of packages before looking globally.
* Added an environment variable `IDRIS2_PACKAGE_PATH` for extending where to
  look for packages.
* Added compiler warnings flags (`-W` prefix):
  - `-Wno-shadowing`: disable shadowing warnings.
  - `-Werror`: treat warnings as errors.
* Experimental flag (`-Xcheck-hashes`) to check hashes instead of filesystem
  times to determine if files should be recompiled. Should help with CI/CD
  caching.

### REPL/IDE mode changes

* Added `:search` command, which searches for functions by type
* `:load`/`:l` and `:cd` commands now only accept paths surrounded by double
  quotes
* Added a timeout to "generate definition" and "proof search" commands,
  defaulting to 1 second (1000 milliseconds) and configurable with
  `%search_timeout <time in milliseconds>`

### Library Changes

#### Prelude

Added

- `Bifoldable` and `Bitraversable` interfaces.
- `Foldable` add `foldlM`, `foldMap`, and `toList`.
- `Monad` interface `>=>`, `<=<` (Kleisli Arrows), and flipped bind (`=<<`).
- `Pair` Applicative and Monad implementations.
- `SnocList` datatype (fliped cons of a linked list).
- `(.:)` function "blackbird operator" (Composition of a two-argument function
  with a single-argument one.)
- `on` function (Eg, ```((+) `on` f) x y = f x + f y```)

Changed

- `===`, `~=~`, and `<+>` operator precedence
- Exctracted `Cast` interface and implementations from `Prelude.Types` to
  `Prelude.Cast`
- Renamed `Data.Strings` to `Data.String`

Hidden

- `countFrom`

#### Base

Added

- `Control.Applicative.Const`.
- New `Control.Monad` Monad Transformers types.
- `Data.Bits`, an interface for bitwise operations.
- `Data.Colist` and `Data.Colist1`.
- `Data.Contravariant` interface for contravariant functors.
- `Data.List` `unzip` function.
- `Data.List1` `zip*` and `unzip*` functions.
- `Data.SnocList`.
- `Data.Stream` `unzipWith` and `unzipWith3` fuctions.
- `Data.Vect` `unzipWith` and `unzipWith3` functions.
- `System.File` `withFile` and total read functions.

Changed:

- Restructured Monad Transformers in `Control.Monad`
- `zip` precedence

#### Contrib

Added

- `Control.Validation`, a library for dependent types input validation.
- `System.Console.GetOpt`, a library for specifying and parsing command line
  options.

#### New test package

- Moved `tests/Lib.idr` to package as `Test/Golden.idr`.
- Removed `contrib/Test/Golden.idr` which duplicated the test framework now in
  the `test` package.

### Codegen changes

#### Racket

* Now always uses `blodwen-sleep` instead of `idris2_sleep` in order to not
  block the Racket runtime when `sleep` is called.
* Redid condition variables in the Racket codegen based on page 5 of the
  Microsoft [Implementing CVs paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2004/12/ImplementingCVs.pdf).
  Previously, they were based on an implementation using semaphores and
  asynchronous channels, which worked apart from `broadcast`. The rework fixes
  `broadcast` at the cost of losing `wait-timeout` due to increased complexity
  of their internals and interactions between their associated functions.

#### JavaScript

* Now use `Number` to represent up to 32 bit precision signed and unsigned
  integers. `Int32` still goes via `BigInt` for multiplication to avoid
  precision issues when getting results larger than `Number.MAX_SAFE_INTEGER`.
  `Bits32` goes via `BigInt` for multiplication for the same reason as well as
  for all bitops, since `Number` uses signed 32 bit integers for those.
* Now use `Number` instead of `BigInt` to represent up to 32 bit fixed precision
  signed and unsigned integers. This should make interop with the FFI more
  straight forward, and might also improve performance.

#### New chez-sep

* This code generator produces many Chez Scheme files and compiles them
  separately instead of producing one huge Scheme program. This significantly
  reduces the amount of memory needed to build large programs. Since this
  backend will skip calling the Chez compiler on modules that haven't changed,
  it also leads to shorter compilation times in large codebases where only some
  files have changed -- for example when developing Idris2 code generators. The
  codegen has a large parallelisation potential but at the moment, it is
  significantly slower for a full rebuild of a large codebase (the code
  generation stage takes about 3x longer).

### API changes

* The API now exposes `Compiler.Separate.getCompilationUnits`, which
  can be used for separate code generation by any backend.
* New fixed precision signed integer types `Int8`, `Int16`, `Int32`,
  and `Int64` where added. In addition, all integral types now properly support
  all arithmetic and bitwise operations.
* The compiler now provides primitive cast operations for all combinations
  of primitives with the exception of going from `Double` to `Char` and
  back, and going from `String` to `Char`.
* A new pragma `%doubleLit` to support overloaded floating point literals
  was added.

### Other changes

* Lots of small performance improvements, some of which may be especially
  noticeable in programs that do a lot of type level evaluation.
* Added HTML documentation generation, using the `--mkdoc` flag
* Support for auto-completion in bash-like shells was added.
* Fixed case-splitting to respect any indentation there may be in the term being
  case-split and the surrounding symbols, instead of filtering out the
  whitespace and putting it back as indentation.

## v0.3.0

Library changes:

* Overhaul of the concurrency primitives:

  - Renamed `System.Concurrency.Raw` to `System.Concurrency`.

  - Modified the implementation of `Prelude.IO.fork` in the Chez Scheme RTS, which
    now returns a semaphore instead of a thread object. This allows the main
    thread to wait for the child thread to finish (see next bullet). The Racket
    implementation already returned a thread descriptor, which could be used to
    wait for the thread to finish.

  - Added `Prelude.IO.threadWait` which waits for a thread, identified by a
    `ThreadID`, to finish. This operation is supported by both the Chez Scheme and
    the Racket RTS'es.

  - Added semaphores to `System.Concurrency`, supported by both the Chez Scheme
    and Racket RTS'es.

  - Added barriers to `System.Concurrency`, supported by both the Chez Scheme
    and Racket RTS'es.

  - Added synchronous channels to `System.Concurrency`, supported by both the Chez
    Scheme and Racket RTS'es.

  - Fixed the support for mutexes in the Racket RTS. Formerly, they were
    implemented with semaphores, and calling`mutexRelease` multiple times would
    increment the internal counter multiple times, allowing multiple concurrent
    `mutexAcquire` operations to succeed simultaneously. Currently, `mutexRelease`
    fails when called on a mutex which isn't owned. (However, `mutexRelease` does
    not check whether the mutex is in fact owned by the current thread, which may
    be a bug.)

  - Modified the support for condition variables in the Racket RTS. Formerly,
    they were implemented using synchronous channels, meaning that:
        + `conditionSignal` was a blocking operation; and
        + calling `conditionSignal` on a condition variable on which no thread
          was waiting would wake the next thread to call `conditionWait`,
          whereas condition variables are supposed to be stateless, and only
          wake threads already in the queue.
    The implementation was replaced with an implementation based on asynchronous
    channels and mutexes, based on the following paper:
    [Implementing Condition Variables with Semaphores](https://www.microsoft.com/en-us/research/wp-content/uploads/2004/12/ImplementingCVs.pdf) by Andrew Birrell

  - Removed `threadID` and `blodwen-thisthread`. Formerly, in the Chez Scheme
    backend, this function returned "the thread ID of the current thread" as a
    value of type `ThreadID`. However, `fork` returned a "thread object" as a
    value of type `ThreadID`. These are *different kinds of values* in Chez
    Scheme. As there was nothing one could do with a value of type `ThreadID`, I
    chose to remove `threadID`, as it allowed me to implement `threadWait` more
    easily.

  - Renamed `blodwen-lock` and `blodwen-unlock` to `blodwen-mutex-acquire` and
    `blodwen-mutex-release` for consistency, as these functions are referred to
    with acquire and release both in Chez Scheme and in the Idris2 concurrency
    module.

* Added `Data.HVect` in `contrib`, for heterogeneous vectors.
* Various other library functions added throughout `base` and `contrib`

Command-line options changes:

* Added `--color` and `--no-color` options for colored terminal output.
  Color is enabled by default.
* Added `--console-width <auto|n>` option for printing margins.  By default the
  `auto` option is selected, the result is that the compiler detects the current
  terminal width and sets it as the option value, otherwise a user value can be
  provided.  An explicit `0` has the effect of simulating a terminal with
  unbounded width.

Language and compiler changes:

* Removed multiplicity subtyping, as this is unsound and unfortunately causes
  more problems than it solves. This means you sometimes now need to write
  linear versions of functions as special cases. (Though note that the 1
  multiplicity is still considered experimental, so hopefully this will change
  for the better in the future!)
* Added new syntax for named applications of explicit arguments:

     `f {x [= t], x [= t], ...}`
     `f {x [= t], x [= t], ..., _}`

* Added syntax for binding all explicit arguments (in the left hand side);

     `f {}`

* Added new syntax for record updates (without the need for the `record`
  keyword):

     `{x := t, x $= t, ...}`

* Local implementations of interfaces (in `let` or `where` blocks) now work,
  along with `%hint` annotations on local definitions, meaning that local
  definitions can be searched in auto implicit search.
  + Note, though, that there are still some known limitations (with both local
    hints and local implementations) which will be resolved in the next version.
* New experimental ``refc`` code generator, which generates C with reference
  counting.
* Added primitives to the parsing library used in the compiler to get more precise
  boundaries to the AST nodes `FC`.

REPL/IDE mode changes:

* Added `:color (on|off)` option for colored terminal output.
* Added `:consolewidth (auto|n)` option for printing margins.  Mirrors the
  command-line option.

## v0.2.1

Language changes:

* `Bits8`, `Bits16`, `Bits32` and `Bits64` primitive types added, with:
  + `Num`, `Eq`, `Ord` and `Show` implementations.
  + Casts from `Integer`, for literals
  + Casts to `Int` (except for `Bits64` which might not fit),
    `Integer` and `String`
  + Passed to C FFI as `unsigned`
  + Primitives added in `Data.Buffer`
* Elaborator reflection and quoting terms
  + Requires extension `%language ElabReflection`
  + API defined in `Language.Reflection`, including functions for getting
    types of global names, constructors of data types, and adding new top
    level declarations
  + Implemented `%macro` function flag, to remove the syntactic noise of
    invoking elaborator scripts. This means the function must always
    be fully applied, and is run under `%runElab`
* Add `import X as Y`
  + This imports the module `X`, adding aliases for the definitions in
    namespace `Y`, so they can be referred to as `Y`.
* `do` notation can now be qualified with a namespace
  + `MyDo.do` opens a `do` block where the `>>=` operator used is `MyDo.(>>=)`

Library changes:

* `IO` operations in the `prelude` and `base` libraries now use the
  `HasIO` interface, rather than using `IO` directly.
* Experimental `Data.Linear.Array` added to `contrib`, supporting mutable
  linear arrays with constant time read/write, convertible to immutable arrays
  with constant time read.
  + Anything in `Data.Linear` in `contrib`, just like the rest of `contrib`,
    should be considered experimental with the API able to change at any time!
    Further experiments in `Data.Linear` are welcome :).
* Experimental `Control.Linear.LIO` added to `contrib`, supporting computations
  which track the multiplicities of their return values, which allows linear
  resources to be tracked.
* Added `Control.Monad.ST`, for update in-place via `STRef` (which is like
  `IORef`, but can escape from `IO`). Also added `Data.Ref` which provides an
  interface to both `IORef` and `STRef`.
* Added `Control.ANSI` in `contrib`, for usage of ANSI escape codes for text
  styling and cursor/screen control in terminals.

Command-line options changes:

* Removed `--ide-mode-socket-with` option.  `--ide-mode-socket` now accepts an
  optional `host:port` argument.
* Added options to override source directory, build directory and output
  directory: `--source-dir`, `--build-dir`, `--output-dir`.
  + These options are also available as fields in the package description:
    `sourcedir`, `builddir`, `outputdir`.

Compiler changes:

* It is now possible to create new backends with minimal overhead.
  `Idris.Driver` exposes the function `mainWithCodegens` that takes
  a list of codegens. The feature in documented [here](https://idris2.readthedocs.io/en/latest/backends/custom.html).
* New code generators `node` and `javascript`.

REPL/IDE mode changes:

* Implemented `:module` command, to load a module during a REPL session.
* Implemented `:doc`, which displays documentation for a name.
* Implemented `:browse`, which lists the names exported by a namespace.
* Added `:psnext`, which continues the previous proof search, looking for the
  next type correct expression
  + Correspondingly, added the IDE mode command `proof-search-next` (which takes
    no arguments)
* Added `:gdnext`, which continues the previous program search, looking for the
  next type correct implementation
  + Correspondingly, added the IDE mode command `generate-def-next` (which takes
    no arguments)
* Improved program search to allow deconstructing intermediate values, and in
  simple cases, the result of recursive calls.

## v0.2.0

The implementation is now self-hosted. To initialise the build, either use
the [bootstrapping version of Idris2](https://github.com/edwinb/Idris2-boot)
or build from the generated Scheme, using `make bootstrap`.

Language changes:

* `total`, `covering` and `partial` flags on functions now have an effect.
* `%default <totality status>` has been implemented. By default, functions must
  be at least `covering`
  + That is, `%default covering` is the default status.
* Fields of records can be accessed (and updated) using the dot syntax,
  such as `r.field1.field2` or `record { field1.field2 = 42 }`.
  For details, see [the "records" entry in the user manual](https://idris2.readthedocs.io/en/latest/reference/records.html)
* New function flag `%tcinline` which means that the function should be
  inlined for the purposes of totality checking (but otherwise not inlined).
  This can be used as a hint for totality checking, to make the checker look
  inside functions that it otherwise might not.
* %transform directive, for declaring transformation rules on runtime
  expressions. Transformation rules are automatically added for top level
  implementations of interfaces.
* A %spec flag on functions which allows arguments to be marked for partial
  evaluation, following the rules from "Scrapping Your Inefficient Engine"
  (ICFP 2010, Brady & Hammond)
* To improve error messages, one can use `with NS.name <term>`
  or `with [NS.name1, NS.name2, ...] <term>` to disable disambiguation
  for the given names in `<term>`. Example: `with MyNS.(>>=) do ...`.

Library additions:

* Additional file management operations in `base`
* New module in `base` for time (`System.Clock`)
* New modules in `contrib` for JSON (`Language.JSON.*`); random numbers
  (`System.Random`)

Compiler updates:

* Data types with a single constructor, with a single unerased arguments,
  are translated to just that argument, to save repeated packing and unpacking.
  (c.f. `newtype` in Haskell)
  + A data type can opt out of this behaviour by specifying `noNewtype` in its
    options list. `noNewtype` allows code generators to apply special handling
    to the generated constructor/deconstructor, for a newtype-like data type,
    that would otherwise be optimised away.
* 0-multiplicity constructor arguments are now properly erased, not just
  given a placeholder null value.

Other improvements:

* Various performance improvements in the typechecker:
  + Noting which metavariables are blocking unification constraints, so that
    they only get retried if those metavariables make progress.
  + Evaluating `fromInteger` at compile time.
* Extend Idris2's literate mode to support reading Markdown and OrgMode files.
  For more details see: ["literate" in the user manual](https://idris2.readthedocs.io/en/latest/reference/literate.html).

## Changes since Idris 1

Everything :). For full details, see:
[updates](https://idris2.readthedocs.io/en/latest/updates/updates.html)
