module TestNumeric

-- Exhaustive edge-case tests for every numeric type in the RefC backend.
-- Covers: bounds, overflow wrapping, GMP large integers, IEEE 754 specials.

-- Int (64-bit signed on 64-bit targets) ------------------------------------
testInt : IO ()
testInt = do
  putStrLn "=== Int ==="
  let zero  : Int = 0
  let imax  : Int = 9223372036854775807
  let imin  : Int = -9223372036854775808
  printLn zero
  printLn imax
  printLn imin
  printLn (imax + 1)   -- wraps to imin
  printLn (imin - 1)   -- wraps to imax

-- Int8 / Int16 / Int32 / Int64 ---------------------------------------------
testInt8 : IO ()
testInt8 = do
  putStrLn "=== Int8 ==="
  let lo : Int8 = -128
  let hi : Int8 = 127
  printLn lo
  printLn hi
  printLn (hi + 1)  -- -128
  printLn (lo - 1)  -- 127

testInt16 : IO ()
testInt16 = do
  putStrLn "=== Int16 ==="
  let lo : Int16 = -32768
  let hi : Int16 = 32767
  printLn lo
  printLn hi
  printLn (hi + 1)
  printLn (lo - 1)

testInt32 : IO ()
testInt32 = do
  putStrLn "=== Int32 ==="
  let lo : Int32 = -2147483648
  let hi : Int32 = 2147483647
  printLn lo
  printLn hi
  printLn (hi + 1)
  printLn (lo - 1)

testInt64 : IO ()
testInt64 = do
  putStrLn "=== Int64 ==="
  let lo : Int64 = -9223372036854775808
  let hi : Int64 = 9223372036854775807
  printLn lo
  printLn hi
  printLn (hi + 1)
  printLn (lo - 1)

-- Bits8 / Bits16 / Bits32 / Bits64 -----------------------------------------
testBits8 : IO ()
testBits8 = do
  putStrLn "=== Bits8 ==="
  let z : Bits8 = 0
  let m : Bits8 = 255
  printLn z
  printLn m
  printLn (m + 1)   -- 0
  printLn (z - 1)   -- 255

testBits16 : IO ()
testBits16 = do
  putStrLn "=== Bits16 ==="
  let z : Bits16 = 0
  let m : Bits16 = 65535
  printLn z
  printLn m
  printLn (m + 1)
  printLn (z - 1)

testBits32 : IO ()
testBits32 = do
  putStrLn "=== Bits32 ==="
  let z : Bits32 = 0
  let m : Bits32 = 4294967295
  printLn z
  printLn m
  printLn (m + 1)
  printLn (z - 1)

testBits64 : IO ()
testBits64 = do
  putStrLn "=== Bits64 ==="
  let z : Bits64 = 0
  let m : Bits64 = 18446744073709551615
  printLn z
  printLn m
  printLn (m + 1)
  printLn (z - 1)

-- Integer (arbitrary precision via GMP) ------------------------------------
testInteger : IO ()
testInteger = do
  putStrLn "=== Integer ==="
  let a : Integer = 0
  let b : Integer = 9223372036854775808     -- 2^63, above Int64 max
  let c : Integer = -9223372036854775809    -- below Int64 min
  let d : Integer = 123456789012345678901234567890
  printLn a
  printLn b
  printLn c
  printLn d
  printLn (d * 2)

-- Double -------------------------------------------------------------------
testDouble : IO ()
testDouble = do
  putStrLn "=== Double ==="
  let z : Double = 0.0
  let p : Double = 1.0
  let n : Double = -1.0
  printLn z
  printLn p
  printLn n
  printLn (p / z)   -- +Inf
  printLn (n / z)   -- -Inf
  printLn (z / z)   -- NaN

main : IO ()
main = do
  testInt
  testInt8
  testInt16
  testInt32
  testInt64
  testBits8
  testBits16
  testBits32
  testBits64
  testInteger
  testDouble
