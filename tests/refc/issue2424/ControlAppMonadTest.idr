module Main

import Control.App
import Control.App.Console
import Control.Monad.Either



data MyStateName : Type where

fct_b : Has [PrimIO, State MyStateName Nat] es => App es ()
fct_b  = do
    g <- get MyStateName
    primIO $ putStrLn $ "value is " ++ (show g)
    pure ()


fct_a : Has [PrimIO] es => App es ()
fct_a = new 42 fct_b


main : IO ()
main = run fct_a
