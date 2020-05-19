showIfEq : (Eq a, Show a) => a -> a -> String
showIfEq x y = if x == y then show x else "Nope"

topeq : Eq a => a -> a -> Bool
topeq x y = x == y

data Foo = MkFoo | MkBar

-- Should only show the first interface search failure in the tuple
-- (Ideally it would keep going and find all the failures, but that is
-- hard to achieve and this way is better than displaying the whole
-- top level search when only part of it is relevant)

test : Int -> String
test x = showIfEq MkFoo MkBar

Eq Foo where
  MkFoo == MkFoo = True
  MkBar == MkBar = True
  _ == _ = False

test2 : String
test2 = showIfEq MkFoo MkBar

