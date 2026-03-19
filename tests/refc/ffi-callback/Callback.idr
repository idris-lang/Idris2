-- RefC FFI callback test.
-- Tests that Idris closures can be passed to C as typed function pointers.
import System.FFI

pfn : String -> String
pfn fn = "C:" ++ fn ++ ",libcallback,callback.h"

-- int64_t sum_of(int n, int64_t (*f)(int64_t))
%foreign (pfn "sum_of")
prim__sumOf : Int -> (Int -> Int) -> Int

-- int64_t sum_two(int n, int64_t (*f)(int64_t), int64_t (*g)(int64_t))
%foreign (pfn "sum_two")
prim__sumTwo : Int -> (Int -> Int) -> (Int -> Int) -> Int

main : IO ()
main = do
    -- squares: 0^2 + 1^2 + 2^2 + 3^2 + 4^2 = 30
    let s1 = prim__sumOf 5 (\x => x * x)
    putStrLn $ "sum squares 0..4 = " ++ show s1   -- 30

    -- identity: 0+1+2+3+4 = 10
    let s2 = prim__sumOf 5 (\x => x)
    putStrLn $ "sum id 0..4 = " ++ show s2         -- 10

    -- double: 0+2+4+6+8 = 20
    let s3 = prim__sumOf 5 (* 2)
    putStrLn $ "sum double 0..4 = " ++ show s3     -- 20

    -- closure over external value
    let offset = the Int 100
    let s4 = prim__sumOf 3 (+ offset)              -- (100+101+102) = 303
    putStrLn $ "sum (+100) 0..2 = " ++ show s4

    -- re-entrancy: two distinct closures of the same type active simultaneously
    -- sum_two 3 (*2) (*3) = sum_i (2i + 3i) for i in [0,2] = 0+5+10 = 15
    let s5 = prim__sumTwo 3 (* 2) (* 3)
    putStrLn $ "sum_two (*2) (*3) 0..2 = " ++ show s5  -- 15

    putStrLn "done"
