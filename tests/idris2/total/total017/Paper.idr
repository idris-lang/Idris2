-- The size-change principle for program termination
-- https://doi.org/10.1145/360204.360210

%default total

-- Ex 1
mutual
  rev : List Integer -> List Integer
  rev ls = r1 ls []

  r1 : List Integer -> List Integer -> List Integer
  r1 [] a = a
  r1 (x :: xs) a = r1 xs (x :: xs)

-- Ex 2
mutual
  f2 : Nat -> Nat -> Nat
  f2 0 x = x
  f2 i@(S i') x = g2 i' x i

  g2 : Nat -> Nat -> Nat -> Nat
  g2 a b c = f2 a (b + c)

-- Ex 3
a : Nat -> Nat -> Nat
a 0 n = n+1
a (S m) 0 = a m 1
a (S m) (S n) = a m (a (S m) n)

-- Ex 4
p : Nat -> Nat -> Nat -> Nat
p m n (S r) = p m r n
p m (S n) r = p r n m
p m n r = m

-- Ex 5
f5 : List Integer -> List Integer -> List Integer
f5 xs [] = xs
f5 [] ys@(_ :: ys') = f5 ys ys'
f5 xs@(_ :: xs') ys@(_ :: ys') = f5 ys xs'

-- Ex 6
mutual
  f6 : List Integer -> List Integer -> List Integer
  f6 as [] = g6 as []
  f6 as (b :: bs) = f6 (b :: as) bs

  g6 : List Integer -> List Integer -> List Integer
  g6 [] ds = ds
  g6 (c :: cs) ds = g6 cs (c :: ds)
