module Main

import Foo

testConstValue1 : String
testConstValue1 = dep1

testConstValue2 : String
testConstValue2 = dep2

testFunctionPass : String -> String
testFunctionPass = dep3

testErasedFunction : List Int -> Foo.foo Int
testErasedFunction xs = xs

0 testInErasedContext : Type
testInErasedContext = foo Int

