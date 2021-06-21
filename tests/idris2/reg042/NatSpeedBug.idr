module NatSpeedBug

import System
import System.Clock
import Data.List
import Data.Nat
import Data.String

timeit : Lazy x -> IO (x,Clock Duration)
timeit x =
  do
    start <- clockTime Monotonic
    let x' = force x
    end <- clockTime Monotonic
    pure (x', timeDifference end start)

v1 : Nat
v1 = 100000000

v2 : Nat
v2 = 100000000

v3 : Nat
v3 = 100000001

test : List (Lazy Bool)
test =
 [
   --fast ops
   delay $ (natToInteger $ v1 + v2) == 200000000
  ,delay $ (natToInteger $ 2 * v1) ==  200000000
  ,delay $ (v1 `minus` v2) == 0    --should be fast, but is slow
  ,delay $ (natToInteger v1) ==      100000000
  ,delay $ const True (integerToNat  100000000)
 ]

toNano : Clock type -> Integer
toNano (MkClock seconds nanoseconds) =
  let scale = 1000000000
   in scale * seconds + nanoseconds

main : IO ()
main =
  do
    cutOff <- getCutoffArg
    ignore $ traverse (prnIt cutOff) (zip [0..length test] test)
    pure ()
  where
    getCutoffArg : IO (Maybe Integer)
    getCutoffArg =
      do
        args <- getArgs
        let (_ :: cutoffStr :: _) = args
               | x => pure Nothing
        let cutOff = cast $ stringToNatOrZ cutoffStr
        pure $ if cutOff == 0 then Nothing else Just cutOff

    showit : Bool -> String -> String -> String
    showit v a b = if v then a else b
    prnIt : (Maybe Integer) -> (Nat, Lazy Bool) -> IO ()
    prnIt mCutOff (ind, lb) =
        do
          (b, diff) <- timeit lb
          putStrLn $ (show ind) ++ ": " ++ showit b "Pass" "Fail" ++ " " ++
             maybe
               (show diff)
               (\co => showit (toNano diff < co) "Fast" "Slow")
               mCutOff
