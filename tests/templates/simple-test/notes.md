## Description

Template for simpler tests where we need to check or compile single modules. For tests that require a package, see the
template `with-ipkg`.

### Mandatory steps
* Create a new subdirectory for the tests. Try to adhere to the naming scheme of existing tests.
* Update the `tests/Main.idr`, adding the new subdirectory to the lists of tests.
* In the `run` script, the compiler location is bound to `$1` and all calls must have the `--no-color --console-width 0
--no-banner` flags to avoid system dependent differences. Also keep the `rm -rf build` line as keeping build files can
lead unexpected differences in the output, due to compiler logs and not errors.
* If the tests open a REPL session, remember to put a quit command, `:q`in the input file.
* The files named `run`, `expected`, `output` are reserved by the test runner, do not overwrite them by running the test.

### Optional steps
* The expected file can be updated for the first time manually, or by running the test, after updating `tests/Main.idr`,
with `make test only="testdir/testname000"` (substitute the only arguments with the subdirectory of the test).
