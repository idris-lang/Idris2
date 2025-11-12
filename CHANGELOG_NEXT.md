# Changelog Next

This CHANGELOG describes the merged but unreleased changes.  Please see
[CHANGELOG](./CHANGELOG.md) for changes to all previously released versions of
Idris2, as well as the sub-headings typically used for changes.  All new PRs
should target this file (`CHANGELOG_NEXT`).

## [Next version]

### Compiler changes

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

### Building/Packaging changes

* Fix parsing of capitalised package names containing hyphens.

### Backend changes

#### RefC Backend

* Fixed an issue to do with `alligned_alloc` not existing on older MacOS
  versions, causing builds targeting PowerPC to fail (#3662).  For these
  systems, the compiler will now use `posix_memalign`.
