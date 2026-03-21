-- Test that --directive no-ffi produces a working binary for programs
-- that do not require libffi (i.e. no CFFun foreign callbacks).
-- The no-ffi flag omits -lffi from the linker invocation, which is
-- necessary for targets where libffi is unavailable (embedded, WASM, etc.).

module NoFFI

import Data.List

sum' : List Int -> Int
sum' = foldl (+) 0

main : IO ()
main = do
  putStrLn "no-ffi build: OK"
  printLn (sum' [1..10])
  printLn (length (filter (\x => x `mod` 2 == 0) [1..100]))
