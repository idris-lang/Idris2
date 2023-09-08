import Data.List

ack : Nat -> Nat -> Nat
ack 0 n = S n
ack (S k) 0 = ack k 1
ack (S j) (S k) = ack j (ack (S j) k)

foo : Nat -> Nat
foo Z = Z
foo (S Z) = (S Z)
foo (S (S k)) = foo (S k)

data Ord = Zero | Suc Ord | Sup (Nat -> Ord)

ordElim : (x : Ord) ->
          (p : Ord -> Type) ->
          (p Zero) ->
          ((x : Ord) -> p x -> p (Suc x)) ->
          ((f : Nat -> Ord) -> ((n : Nat) -> p (f n)) ->
             p (Sup f)) -> p x
ordElim Zero p mZ mSuc mSup = mZ
ordElim (Suc o) p mZ mSuc mSup = mSuc o (ordElim o p mZ mSuc mSup)
ordElim (Sup f) p mZ mSuc mSup =
   mSup f (\n => ordElim (f n) p mZ mSuc mSup)

mutual
  bar : Nat -> Lazy Nat -> Nat
  bar x y = mp x y

  mp : Nat -> Nat -> Nat
  mp Z y = y
  mp (S k) y = S (bar k y)

mutual
    swapR : Nat -> Nat -> Nat
    swapR x (S y) = swapL y x
    swapR x Z = x

    swapL : Nat -> Nat -> Nat
    swapL (S x) y = swapR y (S x)
    swapL Z y = y

loopy : a
loopy = loopy

data Bin = EPS | C0 Bin | C1 Bin

foom : Bin -> Nat
foom EPS = Z
foom (C0 EPS) = Z
foom (C0 (C1 x)) = S (foom (C1 x))
foom (C0 (C0 x)) = foom (C0 x)
foom (C1 x) = S (foom x)

pfoom : Bin -> Nat
pfoom EPS = Z
pfoom (C0 EPS) = Z
pfoom (C0 (C1 x)) = S (pfoom (C0 x))
pfoom (C0 (C0 x)) = pfoom (C0 x)
pfoom (C1 x) = S (foom x)

even : Nat -> Bool
even Z = True
even (S k) = odd k
  where
    odd : Nat -> Bool
    odd Z = False
    odd (S k) = even k

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

vtrans : Vect n a -> Vect n a -> List a
vtrans [] _         = []
vtrans (x :: xs) ys = x :: vtrans ys ys

data GTree : Type -> Type where
     MkGTree : List (GTree a) -> GTree a

size : GTree a -> Nat
size (MkGTree []) = Z
size (MkGTree xs) = sizeAll xs
  where
    plus : Nat -> Nat -> Nat
    plus Z y = y
    plus (S k) y = S (plus k y)

    sizeAll : List (GTree a) -> Nat
    sizeAll [] = Z
    sizeAll (x :: xs) = plus (size x) (sizeAll xs)

qsortBad : Ord a => List a -> List a
qsortBad [] = []
qsortBad (x :: xs)
   = qsortBad (filter (< x) xs) ++ x :: qsortBad (filter (> x) xs)

qsort : Ord a => List a -> List a
qsort [] = []
qsort (x :: xs)
   = qsort (assert_smaller (x :: xs) (filter (< x) xs)) ++
         x :: qsort (assert_smaller (x :: xs) (filter (> x) xs))

qsort' : Ord a => List a -> List a
qsort' [] = []
qsort' (x :: xs)
   = let (xs_low, xs_high) = partition x xs in
         qsort' (assert_smaller (x :: xs) xs_low) ++
         x :: qsort' (assert_smaller (x :: xs) xs_high)
  where
    partition : a -> List a -> (List a, List a)
    partition x xs = (filter (< x) xs, filter (>= x) xs)

mySorted : Ord a => List a -> Bool
mySorted []      = True
mySorted (x::xs) =
  case xs of
    Nil     => True
    (y::ys) => x <= y && mySorted (y::ys)

myMergeBy : (a -> a -> Ordering) -> List a -> List a -> List a
myMergeBy order []      right   = right
myMergeBy order left    []      = left
myMergeBy order (x::xs) (y::ys) =
  case order x y of
       LT => x :: myMergeBy order xs (y::ys)
       _  => y :: myMergeBy order (x::xs) ys
