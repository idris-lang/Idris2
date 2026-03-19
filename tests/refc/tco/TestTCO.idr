module TestTCO

-- Tail-call optimisation stress tests for the RefC backend.
--
-- Each test exercises a different path through the trampoline:
--   1. Direct self-recursion (the common case)
--   2. Mutually recursive functions (A → B → A → …)
--   3. Continuation-passing style (higher-order tail calls via closures)
--   4. A function with >16 arguments (FUNStar / vararglist path)
--
-- All tests recurse deeply enough (≥ 1 000 000 steps) that they would
-- overflow the C stack if TCO were not working correctly.

-- 1. Direct tail-recursion ------------------------------------------------

countDown : Int -> Int
countDown 0 = 0
countDown n = countDown (n - 1)

-- 2. Mutual tail-recursion -------------------------------------------------
-- isEven/isOdd bounce between two functions.  A naive implementation would
-- grow the stack by one frame per step; with the trampoline each "bounce"
-- is O(1) stack.

mutual
  isEven : Int -> Bool
  isEven 0 = True
  isEven n = isOdd (n - 1)

  isOdd : Int -> Bool
  isOdd 0 = False
  isOdd n = isEven (n - 1)

-- 3. CPS (higher-order tail calls through closures) -----------------------
-- The trampoline must also handle AApp in tail position via
-- idris2_tailcall_apply_closure.

cpsCounting : Int -> (Int -> Int) -> Int
cpsCounting 0 k = k 0
cpsCounting n k = cpsCounting (n - 1) k

-- 4. >16-argument function (FUNStar dispatch path) -------------------------
-- This function takes 17 parameters; the RefC codegen emits it with the
-- `Value *var_arglist[17]` signature and dispatches it through FUNStar.
-- Tail-recursive so we can verify the FUNStar path is stack-safe.

loop17 : Int ->              -- countdown
         Int -> Int -> Int ->    -- a b c
         Int -> Int -> Int ->    -- d e f
         Int -> Int -> Int ->    -- g h i
         Int -> Int -> Int ->    -- j k l
         Int -> Int -> Int ->    -- m n o
         Int ->                  -- p  (17th arg)
         Int
loop17 0 a b c d e f g h i j k l m n o p = a + b + c + d + e + f +
                                             g + h + i + j + k + l +
                                             m + n + o + p
loop17 cnt a b c d e f g h i j k l m n o p =
  loop17 (cnt - 1) a b c d e f g h i j k l m n o p

-- Main --------------------------------------------------------------------

main : IO ()
main = do
  -- 1. Direct self-recursion: 1 000 000 steps
  let r1 = countDown 1000000
  putStrLn $ "countDown 1000000 = " ++ show r1

  -- 2. Mutual recursion: 1 000 000 steps
  let r2 = isEven 1000000
  putStrLn $ "isEven 1000000 = " ++ show r2

  -- 3. CPS: 1 000 000 steps
  let r3 = cpsCounting 1000000 id
  putStrLn $ "cpsCounting 1000000 = " ++ show r3

  -- 4. >16 args / FUNStar path: 1 000 000 steps
  let r4 = loop17 1000000 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
  putStrLn $ "loop17 1000000 = " ++ show r4
