
This CHANGELOG describes the merged but unreleased changes. Please see [CHANGELOG](./CHANGELOG.md) for changes to all previously released versions of Idris2. All new PRs should target this file (`CHANGELOG_NEXT`).

# Changelog

## [Next version]

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

### Language changes

* Autobind and Typebind modifier on operators allow the user to
  customise the syntax of operator to look more like a binder.
  See [#3113](https://github.com/idris-lang/Idris2/issues/3113).

* Fixity declarations without an export modifier now emit a warning in peparation
  for a future version where they will become private by default.

* Elaborator scripts were made to be able to access the visibility modifier of a
  definition, via `getVis`.

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

* LHS of `with`-applications are parsed as `PWithApp` instead of `PApp`. As a
  consequence, `IWithApp` appears in `TTImp` values in elaborator scripts instead
  of `IApp`, as it should have been.

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

* Supress code generation of _arglist wrappers to reduce code size and compilation time.

* Removed Value_Arglist to reduce Closure's allocation overhead and make code simply.

* Switch calling conventions based on the number of arguments to avoid limits on
  the number of arguments and to reduce stack usage.

#### Chez

* Fixed CSE soundness bug that caused delayed expressions to sometimes be eagerly
  evaluated. Now when a delayed expression is lifted by CSE, it is compiled
  using Scheme's `delay` and `force` to memoize them.

#### Racket

* Fixed CSE soundness bug that caused delayed expressions to sometimes be eagerly
  evaluated. Now when a delayed expression is lifted by CSE, it is compiled
  using Scheme's `delay` and `force` to memoize them.

#### NodeJS Backend

* The NodeJS executable output to `build/exec/` now has its executable bit set.
  That file already had a NodeJS shebang at the top, so now it is fully ready to
  go after compilation.

### Library changes

#### Prelude

#### Base

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

* Implemented `leftMost` and `rightMost` for `SortedSet`.

* Added `funExt0` and `funExt1`, functions analogous to `funExt` but for functions
  with quantities 0 and 1 respectively.

* `SortedSet`, `SortedMap` and `SortedDMap` modules were extended with flipped variants
  of functions like `lookup`, `contains`, `update` and `insert`.

* Moved definition of `Data.Vect.nubBy` to the global scope as `nubByImpl` to
  allow compile time proofs on `nubBy` and `nub`.

* Removed need for the runtime value of the implicit length argument in
  `Data.Vect.Elem.dropElem`.

#### Contrib

* `Data.List.Lazy` was moved from `contrib` to `base`.

* Existing `System.Console.GetOpt` was extended to support errors during options
  parsing in a backward-compatible way.

* Moved helpers from `Data.HVect` to base library's `Data.Vect.Quantifiers.All`
  and removed `Data.HVect` from contrib. See the additional notes in the
  CHANGELOG under the `Library changes`/`Base` section above.

#### Network

* Add a missing function parameter (the flag) in the C implementation of `idrnet_recv_bytes`
