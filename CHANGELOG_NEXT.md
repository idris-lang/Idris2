
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

* The Nix flake now exposes the Idris2 API package as `idris2-api` and Idris2's
  C support library as `support`.

### Language changes

### Compiler changes

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

#### Contrib

* `Data.List.Lazy` was moved from `contrib` to `base`.

* Existing `System.Console.GetOpt` was extended to support errors during options
  parsing in a backward-compatible way.

* Moved helpers from `Data.HVect` to base library's `Data.Vect.Quantifiers.All`
  and removed `Data.HVect` from contrib. See the additional notes in the
  CHANGELOG under the `Library changes`/`Base` section above.

