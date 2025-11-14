# Changelog Next

This CHANGELOG describes the merged but unreleased changes.  Please see
[CHANGELOG](./CHANGELOG.md) for changes to all previously released versions of
Idris2, as well as the sub-headings typically used for changes.  All new PRs
should target this file (`CHANGELOG_NEXT`).

## [Next version]

### Building/Packaging changes

* Fix parsing of capitalised package names containing hyphens.

### Backend changes

### Compiler changes

* Fixes an issue when unifying labmda terms with implicits (#3670)

#### RefC Backend

* Fixed an issue to do with `alligned_alloc` not existing on older MacOS
  versions, causing builds targeting PowerPC to fail (#3662).  For these
  systems, the compiler will now use `posix_memalign`.
