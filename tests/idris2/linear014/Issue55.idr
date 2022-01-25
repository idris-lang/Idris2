0
foo : (0 b : Bool) -> Bool
foo b = b

0
bar : Bool
bar = q
  where
    q : Bool
    q = foo True

0
baz : Bool
baz = let q : Bool
          q = foo True in
      q
