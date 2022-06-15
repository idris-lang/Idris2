f : (0 x : (a,b)) -> Nat
f x =
  let 0 (u,v) = x in
  0

data Foo = Bar Int

g : (0 x : Foo ) -> Nat
g x@(Bar y) = 0

test : (0 _ : (a,b)) -> Nat
test = \ 0 (u,v) => 1

test2 : (0 _ : a = b) -> Nat
test2 = \ 0 Refl => 1

failing
  test3 : (0 _ : (a,b)) -> Nat
  test3 f = let 0 Refl = f in 0
