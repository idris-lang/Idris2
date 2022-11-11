Tests
=====

*Note: The commands listed in this section should be run from the repository's root folder.*

Run all tests: `make test`

To run only a subset of the tests use: `make test only=NAME`. `NAME` is matched against the path to each test case.

Examples:
- `make test only=chez` will run all Chez Scheme tests.
- `make test only=ttimp/basic` will run all basic tests for `TTImp`.
- `make test only=idris2/basic001` will run a specific test.

Templates for common test instances can be found in the `templates` folder.

There is no defined naming convention for adding tests, but the pattern has
been:

- a sub-directory in the relevant test section (`idris2`, `refc`, etc.)
- with a descriptive name followed by a 3-digit number (e.g. `envflags001` is
    the first test checking the environment flags functions)
- containing:
  * an Idris file importing the relevant modules and containing the test
      function(s)
  * a `run` file which is a shell script that runs the test (see the existing
      tests for examples for this)
  * an `expected` file containing the expected output

