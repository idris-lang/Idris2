# Changelog Next

This CHANGELOG describes the merged but unreleased changes.  Please see
[CHANGELOG](./CHANGELOG.md) for changes to all previously released versions of
Idris2, as well as the sub-headings typically used for changes.  All new PRs
should target this file (`CHANGELOG_NEXT`).

## [Next version]

### Compiler changes

* Fixed missing handling of dotted patterns See
  [#3669](https://github.com/idris-lang/Idris2/issues/3669),
  [comment](https://github.com/idris-lang/Idris2/issues/3644#issuecomment-3286320272).
* Removed modules and functions moved to `base`:
  - `Libraries.Data.Fin` → `Data.Fin`
  - `Libraries.Data.IOArray` → `Data.IOArray`
  - `Libraries.Data.List.Extra.minimum` → `Data.List.minimum`
  - `Libraries.Data.List.Lazy` → `Data.List.Lazy`
  - `Libraries.Data.List.Quantifiers.Extra.(++)` → `Data.List.Quantifiers.(++)`
  - `Libraries.Data.List.Quantifiers.Extra.head` → `Data.List.Quantifiers.head`
  - `Libraries.Data.List.Quantifiers.Extra.tail` → `Data.List.Quantifiers.tail`
  - `Libraries.Data.List1` → `Data.List1`
  - `Libraries.Data.SnocList.revOnto` → `Data.SnocList.revOnto`
  - `Libraries.Data.SortedMap` → `Data.SortedMap`
  - `Libraries.Data.SortedSet` → `Data.SortedSet`
  - `Libraries.Utils.Binary.bufferData'` → `Data.Buffer.bufferData'`
* Removed unused functions:
  - `Libraries.Data.List.Extra`: `breakAfter`, `splitAfter` and `zipMaybe`
  - `Libraries.Data.List.Quantifiers.Extra.tabulate`.
  - `Libraries.Utils.Binary.nonEmptyRev`
  - `Libraries.Utils.String.dotSep`
* Fixes an issue when unifying labmda terms with implicits (#3670)
* The compiler now warns the user when `impossible` clauses are ignored. This
  typically happens when a numeric literal or an ambiguous name appears in an
  `impossible` clause.

### Building/Packaging changes

* Fix parsing of capitalised package names containing hyphens.
* Change `flake.nix` to point at `idris-community/idris2-mode` as the URL for
  `inputs.idris-emacs-src` (from the user fork `redfish64/idris2-mode`).

### Backend changes

#### RefC Backend

* Fixed an issue to do with `alligned_alloc` not existing on older MacOS
  versions, causing builds targeting PowerPC to fail (#3662).  For these
  systems, the compiler will now use `posix_memalign`.

### Library changes

#### Base

* Added `rtrim` to `Data.String`.
