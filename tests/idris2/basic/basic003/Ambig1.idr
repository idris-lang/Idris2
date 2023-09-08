data Things : Type where
     MkThings : a -> a -> Things

namespace X
  public export
  data Test = A | B

namespace Y
  public export
  data TestType = Test | Baz

test1 : Things
test1 = MkThings Baz Test

test2 : Things
test2 = MkThings Int Test

test3 : Integer -> Things
test3 x = MkThings Test Baz

test4 : Things
test4 = MkThings Test Int
