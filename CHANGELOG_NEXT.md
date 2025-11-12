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

### Building/Packaging changes

* Fix parsing of capitalised package names containing hyphens.

### Backend changes

#### RefC Backend

* Fixed an issue to do with `alligned_alloc` not existing on older MacOS
  versions, causing builds targeting PowerPC to fail (#3662).  For these
  systems, the compiler will now use `posix_memalign`.
