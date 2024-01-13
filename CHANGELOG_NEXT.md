
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

* The Nix flake now exposes the Idris2 API package as `idris2-api` and Idris2's
  C support library as `support`.

### Language changes

### Compiler changes

### Backend changes

#### RefC

* Supress code generation of _arglist wrappers to reduce code size and compilation time.

* Removed Value_Arglist to reduce Closure's allocation overhead and make code simply.

* Switch calling conventions based on the number of arguments to avoid limits on the number of arguments and to reduce stack usage.

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

#### Contrib

* `Data.List.Lazy` was moved from `contrib` to `base`.

* Existing `System.Console.GetOpt` was extended to support errors during options
  parsing in a backward-compatible way.
