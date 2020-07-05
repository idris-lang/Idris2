module Main

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Maybe
import Data.String.Parser

%default partial
-- Buld this program with '-p contrib'

showRes : Show a => Either String a -> IO ()
showRes res = case res of
                Left err => putStrLn err
                Right xs => printLn xs

-- test lifting
parseStuff : ParseT IO ()
parseStuff = do a <- string "abc"
                lift $ putStrLn "hiya"
                b <- string "def"
                pure ()

-- test a parsing from a pure function
pureParsing : String -> Either String (List Char)
pureParsing str = parse (many (satisfy isDigit)) str



optParser : ParseT IO String
optParser = do res <- option "" (takeWhile isDigit)
               string "def"
               pure $ res

main : IO ()
main = do
    res <- parseT parseStuff "abcdef"
    res <- parseT (string "hi") "hideous"
    case res of
        Left err => putStrLn "NOOOOOOO!"
        Right () => putStrLn "YEEEES!"
    digs <- parseT (satisfy isDigit) "a"
    showRes digs
    migs <- parseT (many (satisfy isDigit)) "766775"
    showRes migs
    showRes $ pureParsing "63553"
    s <- parseT (takeWhile isDigit) "887abc8993"
    showRes s
    res <- parseT optParser "123def"
    showRes res
    res <- parseT optParser "def"
    showRes res
    pure ()