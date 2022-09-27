module TestArgs

import Data.List
import System

main : IO ()
main = getArgs >>= (putStrLn . show . drop 1)
