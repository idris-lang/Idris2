-- Tests that the refc backend's IDRIS2_NO_GMP mode (--directive no-gmp)
-- produces correct results for Integer arithmetic.
--
-- In no-gmp mode, Integer is backed by int64_t instead of GMP mpz_t.
-- Values are bounded to [-2^63, 2^63-1] and overflow wraps.
-- All operations that stay within this range must give the same result
-- as regular GMP-backed Integer.

module NoGMP

put : Show a => a -> IO ()
put = putStrLn . show

-- -----------------------------------------------------------------------
-- 1. Basic arithmetic in-range
-- -----------------------------------------------------------------------

testArith : IO ()
testArith = do
  putStrLn "=== Arithmetic ==="
  put (the Integer 42)
  put (the Integer (1 + 1))
  put (the Integer (100 - 37))
  put (the Integer (6 * 7))
  put (the Integer (100 `div` 7))
  put (the Integer (100 `mod` 7))
  put (the Integer (negate 42))
  put (the Integer (-1000000000 * 1000000000))  -- -10^18, within int64 range

-- -----------------------------------------------------------------------
-- 2. Comparisons
-- -----------------------------------------------------------------------

testCmp : IO ()
testCmp = do
  putStrLn "=== Comparisons ==="
  put (the Integer 0 == 0)
  put (the Integer 1 > 0)
  put (the Integer (-1) < 0)
  put (the Integer 42 >= 42)
  put (the Integer 42 <= 100)
  put (compare (the Integer 1) 2)
  put (compare (the Integer 3) 3)
  put (compare (the Integer 5) 4)

-- -----------------------------------------------------------------------
-- 3. Casts involving Integer
-- -----------------------------------------------------------------------

testCasts : IO ()
testCasts = do
  putStrLn "=== Casts ==="
  -- Integer → String
  put (show (the Integer 9223372036854775807))   -- INT64_MAX
  put (show (the Integer (-9223372036854775808))) -- INT64_MIN
  -- String → Integer
  put (cast {to=Integer} "12345")
  put (cast {to=Integer} "-12345")
  -- Integer → Int64
  put (cast {to=Int64} (the Integer 42))
  put (cast {to=Int64} (the Integer (-1)))
  -- Integer → Bits64
  put (cast {to=Bits64} (the Integer 255))
  -- Double → Integer
  put (cast {to=Integer} (the Double 42.9))
  put (cast {to=Integer} (the Double (-12.001)))
  -- Integer → Double
  put (cast {to=Double} (the Integer 1024))

-- -----------------------------------------------------------------------
-- 4. Bit ops on Integer (no-gmp: operate on int64_t)
-- -----------------------------------------------------------------------

testBits : IO ()
testBits = do
  putStrLn "=== Bit ops ==="
  put (prim__and_Integer 0xFF 0x0F)
  put (prim__or_Integer  0xF0 0x0F)
  put (prim__xor_Integer 0xFF 0x0F)
  put (prim__shl_Integer 1 10)   -- 1024
  put (prim__shr_Integer 1024 3) -- 128

-- -----------------------------------------------------------------------
-- 5. GCD / LCM (should work in-range)
-- -----------------------------------------------------------------------

gcd' : Integer -> Integer -> Integer
gcd' a 0 = a
gcd' a b = gcd' b (a `mod` b)

testGcd : IO ()
testGcd = do
  putStrLn "=== GCD ==="
  put (gcd' 48 18)
  put (gcd' 100 75)
  put (gcd' 1000000007 998244353)

-- -----------------------------------------------------------------------
main : IO ()
main = do
  testArith
  testCmp
  testCasts
  testBits
  testGcd
