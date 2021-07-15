module TestArgs

import System

main : IO ()
main = getArgs >>= (putStrLn . show)
