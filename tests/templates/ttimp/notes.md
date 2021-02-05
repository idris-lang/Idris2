## Description

Template for tests on the `TTImp` representation.

### Mandatory steps
* Create a new subdirectory for the tests. Try to adhere to the naming scheme of existing tests. For `TTImp` files the
convention is to use the `.yaff` extension.
* Update the `tests/Main.idr`, adding the new subdirectory to the lists of tests.
* In the `run` script, Each invocation to the `TTImp` REPL must be prefixed by the `--yaffle` flag. Also keep the `rm -rf build` line as keeping build files can
lead unexpected differences in the output, due to compiler logs and not errors.
* If the tests open a REPL session, remember to put a quit command, `:q`in the input file.
* The files named `run`, `expected`, `output` are reserved by the test runner, do not overwrite them by running the test.

### Optional steps
* The expected file can be updated for the first time manually, or by running the test, after updating `tests/Main.idr`,
with `make test only="testdir/testname000"` (substitute the only arguments with the subdirectory of the test).
* With the `--yaffle` options, the compiler can also read `TTC` files, as show in the template.
