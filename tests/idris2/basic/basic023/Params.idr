parameters (eq : a -> a -> Bool)
  lookup : a -> List (a, b) -> Maybe b
  lookup x [] = Nothing
  lookup x ((k, v) :: ys)
      = if eq x k
           then Just v
           else lookup x ys

  data Dict : Type -> Type where
       MkDict : List (a, b) -> Dict b

  lookupK : a -> Dict b -> Maybe b
  lookupK k (MkDict xs) = lookup k xs

testDict : Dict {a=Int} (==) String
testDict = MkDict _ [(0, "foo"), (1, "bar")]

parameters (y : ?) -- test that the type of 'y' can be inferred
  foo : (x : Int) -> x = y -> Int
  foo x@_ Refl = 42
