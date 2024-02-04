
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

### Backend changes

#### RefC

* Compiler can emit precise reference counting instructions where a reference
  is dropped as soon as possible. This allows you to reuse unique variables and
  optimize memory consumption.

### Compiler changes

#### RefC Backend

* Fix invalid memory read onf strSubStr.

* Fix memory leaks of IORef. Now that IORef holds values by itself,
  global_IORef_Storage is no longer needed.

* Pattern matching generates simpler code. This reduces malloc/free and memory
  consumption. It also makes debugging easier.

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

* Deprecate `bufferData` in favor of `bufferData'`. These functions are the same
  with the exception of the latter dealing in `Bits8` which is more correct than
  `Int`.

#### Contrib

* `Data.List.Lazy` was moved from `contrib` to `base`.

* Existing `System.Console.GetOpt` was extended to support errors during options
  parsing in a backward-compatible way.
