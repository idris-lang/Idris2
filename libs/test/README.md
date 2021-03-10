# Test
The test package exposes the same test framework(s) the Idris 2 compiler uses for its test suite.

In a language like Idris 2, there are a number of strategies one can take for testing their code and the eventual goal of this testing package is to facilitate a blend of these strategies in any project. Currently the package contains one module facilitating one style of testing: `Golden`. Contributions containing other modules that enable additional testing styles are encouraged.

To use the test package, either pass `-p test` to the idris2 executable or add `depends = test` to your test suite's package file.

## Golden
Golden facilitates testing by way of comparing test output with a predetermined expecation. The module is well documented in its own source code but the following is a primer.

You first import the `Test.Golden` module and write an `IO` function to serve as the entrypoint for your test suite. This function must at some point call into Golden's `runner`.
```idris
-- your_project/tests/Main.idr

module Main

import Test.Golden

tests : TestPool

main : IO ()
main = do
  runner [tests]
```

You populate the `TestPool` list that the `runner` expects with one entry per pool of tests you want to run. Within each pool, tests are run concurrently.
```idris
tests : TestPool
tests = MkTestPool [] [
  "my_great_test"
]
```

The first argument to `MkTestPool` (empty in the above example) is a list of codegen backends required to run the tests in the given pool. Any empty list means no requirements. If your tests required the Racket backend, you could instead specify `[Racket]`. See the [`Requirement` type](./Test/Golden.idr#L228) for more.

The second argument to `MkTestPool` is a list of directory names that can be found relative to your `Main.idr` file. This directory will have some combination of the following files.
```Shell
my_great_test/
  Test.idr
  test.ipkg
  expected
  input
  run
```

These files define:
1. Any Idris 2 source code needed for the test (Test.idr, which can be named anything you'd like and is not limited to 1 file).
2. Any package information needed to build those source files (test.ipkg).
3. The command run at the shell to execute your test (run).
4. Optional input passed to your test case (input).
5. The expected output of running your test (expected).

See the [documentation](./Test/Golden.idr#L12) in `Test/Golden.idr` and the [template directories](../../tests/templates) provided with the Idris 2 project for a great primer on these files.

When you run your tests (the executable produced by building your `tests/Main.idr` file), you need to specify the Idris executable to use and optionally use interactive mode (`--interactive`) or limit the test cases that are run (`--only [names]`).

Interactive mode is useful when you know the expected output for a test case is going to change -- you will be prompted to updated the expectation so you can choose whether the output produced by a new test run should become the new "golden" standard.
You can even skip the step of creating an `expected` file altogether when you write a new test case and use interactive mode to accept the output of your test case as the expectation.

