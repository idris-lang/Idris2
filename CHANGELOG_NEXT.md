
This CHANGELOG describes the merged but unreleased changes. Please see [CHANGELOG](./CHANGELOG.md) for changes to all previously released versions of Idris2. All new PRs should target this file (`CHANGELOG_NEXT`).

# Changelog

## [Next version]

### Language changes

### Compiler changes

### Backend changes

#### RefC

* Supress code generation of _arglist wrappers to reduce code size and compilation time.

* Removed Value_Arglist to reduce Closure's allocation overhead and make code simply.

* Switch calling conventions based on the number of arguments to avoid limits on the number of arguments and to reduce stack usage.

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
