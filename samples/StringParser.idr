module Main

import Data.String.Parser
import Control.Monad.Identity

-- Buld this program with '-p contrib'

partial
main : IO ()
main = do
    res <- parseT (string "hi") "hideous"
    case res of
        Left err => putStrLn "NOOOOOOO!"
        Right () => putStrLn "YEEEES!"
    digs <- parseT (satisfy isDigit) "8878993"
    case digs of
        Left err => putStrLn "NOOOOOOO!"
        Right ds => printLn ds
    migs <- parseT (many (satisfy isDigit)) "766775"
    case migs of
        Left err => putStrLn "NOOOOOOO!"
        Right ds => printLn ds