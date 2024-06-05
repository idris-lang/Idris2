import Data.List.Lazy

import Debug.Trace

%default total

%inline
(::) : Maybe a -> Lazy (LazyList a) -> LazyList a
Nothing :: xs = xs
Just x  :: xs = x :: xs

fufu : a -> Maybe a
fufu = Just

g : LazyList Nat
g = trace "--- outmost ---"
  [ fufu $ trace "pure 6" 6
  , fufu $ trace "pure 5" 5
  ]

main : IO Unit
main = printLn g
