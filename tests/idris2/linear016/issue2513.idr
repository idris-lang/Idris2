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

failing "x is not accessible in this context"
  test6 : (Nat, Nat) -> Nat
  test6 pair = let 0 (x, y) = pair
               in x

record R where
  constructor MkR
  0 erased : Nat
  1 linear : Nat
  omega : Nat

rw0 : R -> Nat
rw0 r = let 0 (MkR e l o) = r in ?foo_w0

rw1 : R -> Nat
rw1 r = let 1 (MkR e l o) = r in ?foo_w1

rwO : R -> Nat
rwO r = let (MkR e l o) = r in ?foo_ww

-- r10 : (1 _ : R) -> R
-- r10 r = let 0 (MkR e l o) = r in ?foo_10

r11: (1 _ : R) -> Nat
r11 r = let 1 (MkR e l o) = r in ?foo_11

r1w : (1 _ : R) -> Nat
r1w r = let (MkR e l o) = r in ?foo_1w
