module Test

import Foo
import Bar
import Baz

main : IO ()
main = putStrLn $ foo ++ bar ++ baz
