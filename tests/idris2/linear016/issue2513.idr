f : (0 x : (a,b)) -> Nat
f x =
  let 0 (u,v) = x in
  0

data Foo = MkFoo Int

g : (0 x : Foo ) -> Nat
g x@(MkFoo y) = 0

test : (0 _ : (a,b)) -> Nat
test = \ 0 (u,v) => 1

-- Lambda can bind erased patterns
test2 : (0 _ : a = b) -> Nat
test2 = \ 0 Refl => 1

-- Lambdas, lets, and dos can bind operators and projection-looking things
test3 : (a -> b) -> (c -> d) -> Maybe Integer
test3 = \ (>>=), (.toD) =>
  let (>>) = 0 in
  let (.inv) = 1 in
  do let (*) = 2
     let (.proj) = 3
     pure 4

failing "Mismatch between: (a, b) and ?_ = ?_."
  test4 : (0 _ : (a,b)) -> Nat
  test4 f = let 0 Refl = f in 0

data Bar : Bool -> Type where
    BarA : Bar True
    BarB : Bar False

test5 : (0 _ : Bar True) -> Unit
test5 x = let 0 BarA = x
          in ()
