f : (0 x : (a,b)) -> Nat
f x =
  let 0 (u,v) = x in
  0

data Foo = Bar Int

g : (0 x : Foo ) -> Nat
g x@(Bar y) = 0

test : (0 _ : (a,b)) -> Nat
test = \ 0 (u,v) => 1

-- Lambda can bind erased patterns
test2 : (0 _ : a = b) -> Nat
test2 = \ 0 Refl => 1

-- Lambda can bind operators
test3 : (a -> b) -> Integer
test3 foo = (\ (>>=) => 0) foo

failing
  test3 : (0 _ : (a,b)) -> Nat
  test3 f = let 0 Refl = f in 0
