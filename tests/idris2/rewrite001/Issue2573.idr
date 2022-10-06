module Issue2573

||| Define foo, the identity function in disguise
foo : Ord a => (x : a) -> a
foo x = if x < x then x else x

||| Assume that foo x = x
eq : Ord a => (a -> a) -> (x : a) -> Issue2573.foo x = x
eq f x = believe_me ()

||| Prove that if x < y then (foo x) < y
prf : Ord a => (a -> a) -> (x, y : a) -> x < y = True -> Issue2573.foo x < y = True
prf f x y lt = rewrite (eq f x) in lt
