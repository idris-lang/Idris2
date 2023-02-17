module Test

import Foo
import Bar
import Baz

||| This test verifies that `.ipkg` can be found after installation and thus
||| transitive dependencies are resolved correctly.
|||
||| This package only depends on package `baz` but also - transitively - on `foo` and `bar`,
||| all of which are accessed in this `main` function.
main : IO ()
main = putStrLn $ foo ++ bar ++ baz
