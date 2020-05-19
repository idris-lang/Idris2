module Main

import Data.Strings
import System

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown (S secs) = do putStrLn (show (S secs))
                        usleep 1000000
                        countdown secs

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
     then pure (Just (stringToNatOrZ input))
     else pure Nothing

countdowns : IO ()
countdowns = do putStr "Enter starting number: "
                Just startNum <- readNumber
                    | Nothing => do putStrLn "Invalid input"
                                    countdowns
                countdown startNum
                putStr "Another (y/n)? "
                yn <- getLine
                if yn == "y" then countdowns
                             else pure ()
