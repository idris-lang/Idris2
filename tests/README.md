Tests
=====

*Note: The commands listed in this section should be run from the repository's root folder.*

Run all tests: `make test`

To run only a subset of the tests use: `make test only=NAME`. `NAME` is matched against the path to each test case.

Examples:
- `make test only=chez` will run all Chez Scheme tests.
- `make test only=ttimp/basic` will run all basic tests for `TTImp`.
- `make test only=idris2/basic001` will run a specific test.
