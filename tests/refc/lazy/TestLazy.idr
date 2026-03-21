module TestLazy

import Data.List.Lazy
import Data.Stream

-- -----------------------------------------------------------------------
-- 1. Infinite Stream (uses Inf / Delay internally)
-- -----------------------------------------------------------------------

myNats : Stream Nat
myNats = go 0
  where
    go : Nat -> Stream Nat
    go n = n :: go (S n)

myIntegers : Stream Integer
myIntegers = go 0
  where
    go : Integer -> Stream Integer
    go n = n :: go (n + 1)

fibs : Stream Integer
fibs = go 0 1
  where
    go : Integer -> Integer -> Stream Integer
    go a b = a :: go b (a + b)

testStream : IO ()
testStream = do
  putStrLn "=== Stream ==="
  printLn (take 5 myNats)
  printLn (take 5 myIntegers)
  printLn (take 8 fibs)

-- -----------------------------------------------------------------------
-- 2. Lazy function arguments: short-circuit must not force the lazy arg
--
-- We use assert_total + local infinite loop as a "poison" lazy value.
-- If the refc backend eagerly forces Lazy args this test will hang.
-- -----------------------------------------------------------------------

lazyAnd : Bool -> Lazy Bool -> Bool
lazyAnd False _ = False
lazyAnd True  r = r

lazyOr : Bool -> Lazy Bool -> Bool
lazyOr True  _ = True
lazyOr False r = r

-- A bottom value: loops forever if forced.
-- assert_total convinces the totality checker this is fine
-- (it never returns, but we never force it in the short-circuit cases).
loop : Lazy Bool
loop = assert_total $ Force loop

testLazyArgs : IO ()
testLazyArgs = do
  putStrLn "=== Lazy arguments ==="
  printLn (lazyAnd False loop)   -- short-circuits: must not force loop
  printLn (lazyOr  True  loop)   -- short-circuits: must not force loop
  printLn (lazyAnd True  True)
  printLn (lazyOr  False False)

-- -----------------------------------------------------------------------
-- 3. Explicit Delay / Force
-- -----------------------------------------------------------------------

testDelayForce : IO ()
testDelayForce = do
  putStrLn "=== Delay / Force ==="
  let x : Lazy Int = Delay 42
  printLn (Force x)
  let y : Lazy String = Delay "hello"
  putStrLn (Force y)

-- -----------------------------------------------------------------------
-- 4. Data.List.Lazy
-- -----------------------------------------------------------------------

isEven : Nat -> Bool
isEven Z     = True
isEven (S k) = not (isEven k)

-- iterate in Data.List.Lazy takes (a -> Maybe a); Just continues, Nothing stops
myNatsL : LazyList Nat
myNatsL = iterate (\n => Just (S n)) 0

testLazyList : IO ()
testLazyList = do
  putStrLn "=== LazyList ==="
  printLn (Lazy.take 6 myNatsL)
  let doubled : LazyList Nat = map (*2) myNatsL
  printLn (Lazy.take 5 doubled)
  let evens : LazyList Nat = filter isEven myNatsL
  printLn (Lazy.take 5 evens)
  -- finite lazy list via iterateN
  let counted : LazyList Nat = iterateN 5 S 0
  printLn (toList counted)

-- -----------------------------------------------------------------------
-- 5. Stream -> LazyList (codata interop)
-- -----------------------------------------------------------------------

streamToLazy : Stream a -> LazyList a
streamToLazy (x :: xs) = x :: streamToLazy xs

testCodata : IO ()
testCodata = do
  putStrLn "=== Codata ==="
  let squares : LazyList Integer =
        map (\n => n * n) (streamToLazy myIntegers)
  printLn (Lazy.take 6 squares)

-- -----------------------------------------------------------------------
main : IO ()
main = do
  testStream
  testLazyArgs
  testDelayForce
  testLazyList
  testCodata
