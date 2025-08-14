
This CHANGELOG describes the merged but unreleased changes. Please see [CHANGELOG](./CHANGELOG.md) for changes to all previously released versions of Idris2. All new PRs should target this file (`CHANGELOG_NEXT`).

# Changelog

## [Next version]

### CLI changes

* The `idris2 --list-packages` command now outputs information about the
  location and available TTC versions for each package it finds. It also shows
  the current Idris2 TTC version so you can spot packages that do not have a
  compatible TTC install. The TTC version tracks breaking changes to the
  compiled binary format of Idris2 code and it is separate from Idris2's
  semantic version (e.g. 0.7.0). A library without the correct TTC version
  installed will be ignored by the compiler when it tries to use that library as
  a dependency for some other package.

* The `idris2 --help pragma` command now outputs the `%hint` pragma.

* The `idris2 --init` command now ensures that package names are
  valid Idris2 identifiers.

* A new `idris2 --dump-installdir {ipkg-filename}` command outputs the file path
  where Idris2 will install the given package if `idris2 --install
  {ipkg-filename}` is called.

* Remove reference to column number parameter in help menu for `refine` command.

* CLI errors will now be printed to `stderr` instead of `stdout`.

* The `idris2 --exec` command now takes an arbitrary expression, not just the
  function name.

* Command-line arguments beginning with `--` which are not a known flag now
  produce an error.

### Building/Packaging changes

* The Nix flake's `buildIdris` function now returns a set with `executable` and
  `library` attributes. These supersede the now-deprecated `build` and
  `installLibrary` attributes. `executable` is the same as `build` and `library`
  is a function that takes an argument determining whether the library should be
  installed with sourcecode files or not; other than that, `library`
  functionally replaces `installLibrary`.

* The Nix flake's `buildIdris` `executable` property (previously `build`) has
  been fixed in a few ways. It used to output a non-executable file for NodeJS
  builds (now the file has the executable bit set). It used to output the
  default Idris2 wrapper for Scheme builds which relies on utilities not
  guaranteed at runtime by the Nix derivation; now it rewraps the output to only
  depend on the directory containing Idris2's runtime support library.

* The Nix flake now exposes the Idris2 API package as `idris2Api` and Idris2's
  C support library as `support`.

* A new `idris2 --dump-ipkg-json` option (requires either `--find-ipkg` or
  specifying the `.ipkg` file) dumps JSON information about an Idris package.

* Support for macOS PowerPC added.

* Multiline comments `{- text -}` are now supported in ipkg files.

### Language changes

* Autobind and Typebind modifier on operators allow the user to
  customise the syntax of operator to look more like a binder.
  See [#3113](https://github.com/idris-lang/Idris2/issues/3113).

* Fixity declarations without an export modifier now emit a warning in peparation
  for a future version where they will become private by default.

* Elaborator scripts were made to be able to access the visibility modifier of a
  definition, via `getVis`.

* The language now has a ``%foreign_impl`` pragma to add additional languages
  to a ``%foreign`` function.

* Bind expressions in `do` blocks can now have a type ascription.
  See [#3327](https://github.com/idris-lang/Idris2/issues/3327).

* Added syntax to specifying quantity for proof in with-clause.

* Old-style parameter block syntax is deprecated in favor of the new one.
  In Idris1 you could write `parameters (a : t1, b : t2)` but this did not
  allow for implicits arguments or quantities, this is deprecated. Use the
  new Idris2 syntax instead where you can write
  `parameters {0 t : Type} (v : t)` to indicate if arguments are implicit or
  erased.

* Elaborator scripts were made to be able to get pretty-printed resugared expressions.

* Fixed unification and conversion of binders with different `PiInfo`.

* `failing` statements with multi-line strings must now use `"""` for the string.

### Compiler changes

* The compiler now differentiates between "package search path" and "package
  directories." Previously both were combined (as seen in the `idris2 --paths`
  output for "Package Directories"). Now entries in the search path will be
  printed under an "Package Search Paths" entry and package directories will
  continue to be printed under "Package Directories." The `IDRIS2_PACKAGE_PATH`
  environment variable adds to the "Package Search Paths." Functionally this is
  not a breaking change.

* The compiler now supports `impossible` in a non-case lambda. You can now
  write `\ Refl impossible`.

* The compiler now parses `~x.fun` as unquoting `x` rather than `x.fun`
  and `~(f 5).fun` as unquoting `(f 5)` rather than `(f 5).fun`.

* Totality checking will now look under data constructors, so `Just xs` will
  be considered smaller than `Just (x :: xs)`.

* LHS of `with`-applications are parsed as `PWithApp` instead of `PApp`. As a
  consequence, `IWithApp` appears in `TTImp` values in elaborator scripts instead
  of `IApp`, as it should have been.

* `MakeFuture` primitive is removed.

* [Typst](https://typst.app/) files can be compiled as Literate Idris.

* `min` was renamed to `leftMost` in `Libraries.Data.Sorted{Map|Set}` in order
  to be defined as in `base`.

* Reflected trees now make use of `WithFC` to replicate the new location tracking
  in the compiler.

* Constructors with certain tags (`CONS`, `NIL`, `JUST`, `NOTHING`) are replaced
  with `_builtin.<TAG>` (eg `_builtin.CONS`). This allows the identity optimisation
  to optimise conversions between list-shaped things.

* [Djot](https://djot.net/) files can now be compiled as CommonMark style
  Literate Idris files.

* Fixed a bug that caused `ttc` size to grow exponentially.

* Removes `prim__void` primitive.
* Fixed `assert_total` operation with coinductive calls

* `IBindVar` supports arbitrary names. `String` in the signature is replaced
  by `Name`.

### Backend changes

#### RefC Backend

* Compiler can emit precise reference counting instructions where a reference
  is dropped as soon as possible. This allows you to reuse unique variables and
  optimize memory consumption.

* Fix invalid memory read in `strSubStr`.

* Fix memory leaks of `IORef`. Now that `IORef` holds values by itself,
  `global_IORef_Storage` is no longer needed.

* Pattern matching generates simpler code. This reduces `malloc`/`free` and memory
  consumption. It also makes debugging easier.

* Stopped useless string copying in the constructor to save memory. Also, name
  generation was stopped for constructors that have tags.

* Special constructors such as `Nil` and `Nothing` were eliminated and assigned to
  `NULL`.

* Unbox `Bits32`, `Bits16`, `Bits8`, `Int32`, `Int16`, `Int8`. These types are now packed into
  Value*. Now, RefC backend requires at least 32 bits for pointers.
  16-bit CPUs are no longer supported. And we expect the address returned by
  `malloc` to be aligned with at least 32 bits. Otherwise it cause a runtime error.

* Rename C function to avoid confliction. But only a part.

* Suppress code generation of `_arglist` wrappers to reduce code size and compilation time.

* Removed `Value_Arglist` to reduce Closure's allocation overhead and make code simply.

* Switch calling conventions based on the number of arguments to avoid limits on
  the number of arguments and to reduce stack usage.

* Values that reference counters reaching their maximum limit are immortalized to
  prevent counter overflow. This can potentially cause memory leaks, but they
  occur rarely and are a better choice than crashing. Since overflow is no longer
  a concern, changing `refCounter` from `int` to `uint16` reduces the size of `Value_Header`.

* Values often found at runtime, such as integers less than 100 are generate
  statically and share.

* Constant `String`, `Int64`, `Bits64` and `Double` values are allocated statically as
  immortal and shared.

* A constant string for the representation of Pi type constructor is defined in
  the support library. Code that creates or pattern-matches on Pi types at
  runtime will now build instead of being rejected by the C compiler.

#### Chez

* Fixed CSE soundness bug that caused delayed expressions to sometimes be eagerly
  evaluated. Now when a delayed expression is lifted by CSE, it is compiled
  using Scheme's `delay` and `force` to memoize them.

* More efficient `collect-request-handler` is used.

* Add a codegen directive called `lazy=weakMemo` to make `Lazy` and `Inf` values *weakly*
  memoised. That is, once accessed, they are allowed to be not re-evaluated until garbage
  collector wipes them.

#### Racket

* Fixed CSE soundness bug that caused delayed expressions to sometimes be eagerly
  evaluated. Now when a delayed expression is lifted by CSE, it is compiled
  using Scheme's `delay` and `force` to memoize them.

* Add a codegen directive called `lazy=weakMemo` to make `Lazy` and `Inf` values *weakly*
  memoised. That is, once accessed, they are allowed to be not re-evaluated until garbage
  collector wipes them.

#### NodeJS Backend

* The NodeJS executable output to `build/exec/` now has its executable bit set.
  That file already had a NodeJS shebang at the top, so now it is fully ready to
  go after compilation.

### Library changes

#### Prelude

* Added pipeline operators `(|>)` and `(<|)`.

* The `void` has been made pure.

#### Base

* `Data.Vect.Views.Extra` was moved from `contrib` to `base`.

* `Data.List.Lazy` was moved from `contrib` to `base`.

* Added an `Interpolation` implementation for primitive decimal numeric types and `Nat`.

* Added append `(++)` for `List` version of `All`.

* Moved helpers and theorems from contrib's `Data.HVect` into base's
  `Data.Vect.Quantifiers.All` namespace. Some functions were renamed and some
  already existed. Others had quantity changes -- in short, there were some
  breaking changes here in addition to removing the respective functions from
  contrib. If you hit a breaking change, please take a look at
  [the PR](https://github.com/idris-lang/Idris2/pull/3191/files) and determine if you
  simply need to update a function name or if your use-case requires additional
  code changes in the base library. If it's the latter, open a bug ticket or
  start a discussion on the Idris Discord to determine the best path forward.

* Deprecate `bufferData` in favor of `bufferData'`. These functions are the same
  with the exception of the latter dealing in `Bits8` which is more correct than
  `Int`.

* Added an alternative `TTImp` traversal function `mapATTImp'` taking the original
  `TTImp` at the input along with already traversed one. Existing `mapATTImp` is
  implemented through the newly added one. The similar alternative for `mapMTTImp`
  is added too.

* Removed need for the runtime value of the implicit argument in `succNotLTEpred`.

* Added utility functions `insertWith`, `insertFromWith` and `fromListWith` for
  `SortedMap`.

* Implemented `leftMost` and `rightMost` for `SortedSet`.

* Added `funExt0` and `funExt1`, functions analogous to `funExt` but for functions
  with quantities 0 and 1 respectively.

* `SortedSet`, `SortedMap` and `SortedDMap` modules were extended with flipped variants
  of functions like `lookup`, `contains`, `update` and `insert`.

* Moved definition of `Data.Vect.nubBy` to the global scope as `nubByImpl` to
  allow compile time proofs on `nubBy` and `nub`.

* Removed need for the runtime value of the implicit length argument in
  `Data.Vect.Elem.dropElem`.

* Some pieces of `Data.Fin.Extra` from `contrib` were moved to `base` to modules
  `Data.Fin.Properties`, `Data.Fin.Arith` and `Data.Fin.Split`.

* `Decidable.Decidable.decison` is now `public export`.

* `Functor` is implemented for `PiInfo` from `Language.Reflection.TT`.

* Quantity of the argument for the type being searched in the `search` function
  from `Language.Reflection` was changed to be zero.

* Added `fromRight` and `fromLeft` for extracting values out of `Either`, equivalent to `fromJust` for `Just`.

* Export `System.Signal.signalCode` and `System.Signal.toSignal`.

* Added implementations of `Foldable` and `Traversable` for `Control.Monad.Identity`

* Added `Data.IORef.atomically` for the chez backend.

* `Data.Nat.NonZero` was made to be an alias for `Data.Nat.IsSucc`.
  `SIsNonZero` was made to be an alias for `ItIsSucc`, was marked as deprecated,
  and won't work on LHS anymore.

* Deprecated `toList` function in favor of `Prelude.toList` in `Data.SortedSet`.

* Several functions like `pop`, `differenceMap` and `toSortedMap` were added to `Data.Sorted{Map|Set}`

* Added `kvList` function to `Data.SortedMap` and `Data.SortedMap.Dependent` to have an unambiguous
  `toList` variant.

* Refactored `Uninhabited` implementation for `Data.List.Elem`, `Data.List1.Elem`, `Data.SnocList.Elem` and `Data.Vect.Elem`
  so it can be used for homogeneous (`===`) and heterogeneous (`~=~`) equality.

* Added `System.Concurrency.channelGetNonBlocking` for the chez backend.

* Added `System.Concurrency.channelGetWithTimeout` for the chez backend.

* Added `System.Concurrency.getThreadId` for the chez backend.

* `unrestricted`, for unpacking a `!* a`, now uses its argument once

* Added default definitions for `zipWith3` and `unzipWith3` in `Zippable`
  interface.

* `Quantifiers` modules for `List`, `Vect`, `LazyList`, `List1` and `SnocList`
  are harmonised among each other. Also, several existing functions related only to
  `All` were moved to appropriate namespace. Couple new functions for `Any` were added.

* Add a function `altAll` connecting `All` to `Any` using `Alternative` to all `Quantifiers` modules.

* Fixed `blodwen-channel-get-with-timeout` implementation with proper recursive call on loop and
  so that it now tracks time spent while attempting to acquire the mutex.

#### Contrib

* `Data.Vect.Views.Extra` was moved from `contrib` to `base`.

* `Data.List.Lazy` was moved from `contrib` to `base`.

* Existing `System.Console.GetOpt` was extended to support errors during options
  parsing in a backward-compatible way.

* Moved helpers from `Data.HVect` to base library's `Data.Vect.Quantifiers.All`
  and removed `Data.HVect` from contrib. See the additional notes in the
  CHANGELOG under the `Library changes`/`Base` section above.

* Some pieces of `Data.Fin.Extra` from `contrib` were moved to `base` to modules
  `Data.Fin.Properties`, `Data.Fin.Arith` and `Data.Fin.Split`.

* Function `invFin` from `Data.Fin.Extra` was deprecated in favour of
  `Data.Fin.complement` from `base`.

* The `Control.Algebra` library from `contrib` has been removed due to being
    broken, unfixed for years, and on several independent occasions causing
    confusion with people picking up Idris and trying to use it.
  - Detailed discussion can be found in
      [Idris2#72](https://github.com/idris-lang/Idris2/issues/72).
  - For reasoning about algebraic structures and proofs, please see
      [Frex](https://github.com/frex-project/idris-frex/) and
      [idris2-algebra](https://github.com/stefan-hoeck/idris2-algebra/).

* Since they depend on `Control.Algebra`, the following `contrib` libraries have
    also been removed:
  - `Control/Monad/Algebra.idr`
  - `Data/Bool/Algebra.idr`
  - `Data/List/Algebra.idr`
  - `Data/Morphisms/Algebra.idr`
  - `Data/Nat/Algebra.idr`

* `prim__makeFuture` from `System.Future` is reimplemented as `%foreign` instead of
  using now removed `MakeFuture` primitive

* The documentation for `Data.Validated.ValidatedL` has been corrected to reflect that
  it uses a `List1` as an error accumulator, not a `List`.

#### Network

* Add a missing function parameter (the flag) in the C implementation of `idrnet_recv_bytes`
* Merge callbacks in linear `newSocket` into one single, linear callback,
  and allow the callback to produce any value

#### Test

* Replaced `Requirement` data type with a new record that can be used to create
  any requirement needed. The constructors for the old `Requirement` type are
  now functions of the same names that return values of the new record type so
  in most situations there should be no compatibility issues.

#### Documentation

* Module docstrings are now displayed for namespace indexes when documentation is built via `--mkdoc`.
* Generated documentation are now removed via `--clean`.
