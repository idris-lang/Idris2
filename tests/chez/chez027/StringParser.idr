module Main

import Control.Monad.Identity
import Control.Monad.Trans

import Data.List.Alternating
import Data.Maybe
import Data.Vect
import Data.String.Parser

%default partial
-- Build this program with '-p contrib'

showRes : Show a => Either String (a, Int) -> IO ()
showRes res = case res of
                Left err => putStrLn err
                Right (xs, rem) => printLn xs

-- test lifting
parseStuff : ParseT IO ()
parseStuff = do a <- string "abc"
                lift $ putStrLn "hiya"
                b <- string "def"
                pure ()

-- test a parsing from a pure function
pureParsing : String -> Either String ((List Char), Int)
pureParsing str = parse (many (satisfy isDigit)) str


-- test option
optParser : ParseT IO String
optParser = do res <- option "" (takeWhile isDigit)
               ignore $ string "def"
               pure $ res

-- test optional
maybeParser : ParseT IO Bool
maybeParser = do res <- optional (string "abc")
                 ignore $ string "def"
                 pure $ isJust res

-- test takeUntil
takeUntilParser : Parser String
takeUntilParser = do ignore $ string "<!--"
                     res <- takeUntil "-->"
                     eos -- To check that takeUntil consumes the stop string itself
                     pure res

main : IO ()
main = do
    res <- parseT parseStuff "abcdef"
    res <- parseT (string "hi") "hiyaaaaaa"
    case res of
        Left err => putStrLn "NOOOOOOO!"
        Right (_, i) => printLn i
    bad <- parseT (satisfy isDigit) "a"
    showRes bad
    bad2 <- parseT (string "good" <?> "Not good") "bad bad bad"
    showRes bad2
    digs <- parseT (many (satisfy isDigit)) "766775"
    showRes digs
    showRes $ pureParsing "63553"
    s <- parseT (takeWhile isDigit) "887abc8993"
    showRes s
    showRes $ parse takeUntilParser "<!--XML Comment-->"
    showRes $ parse takeUntilParser "<!--<- Complicated -- XML -- Comment ->-->"
    showRes $ parse takeUntilParser "<!--Unclosed XML Comment"
    res <- parseT optParser "123def"
    showRes res
    res <- parseT optParser "def"
    showRes res
    res <- parseT maybeParser "abcdef"
    showRes res
    res <- parseT maybeParser "def"
    showRes res
    res <- parseT (commaSep alphaNum) "a,1,b,2"
    showRes res
    res <- parseT (alternating letter natural) "a12b3c"
    showRes res
    res <- parseT (ntimes 4 letter) "abcd"
    showRes res
    res <- parseT (requireFailure letter) "1"
    showRes res
    res <- parseT (requireFailure letter) "a" -- Should error
    showRes res
    pure ()
