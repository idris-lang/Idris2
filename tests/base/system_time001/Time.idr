import System
import Data.String

main : IO ()
main = do systime <- time
          -- sanity checks on time value
          if systime > 1630268000 && systime < 10000000000
             then putStrLn "Retrieved unix timestamp from time function."
             else putStrLn "Failed to retrieve a unix timestamp from time function."
