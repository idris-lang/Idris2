module Main

import Data.String.Parser
import Control.Monad.Identity
import Control.Monad.Trans

%default partial
-- Buld this program with '-p contrib'

parseStuff : ParseT IO ()
parseStuff = do a <- string "abc"
                lift $ putStrLn "hiya"
                b <- string "def"
                pure ()

pureParsing : String -> Either String (List Char)
pureParsing str = parse (many (satisfy isDigit)) str

main : IO ()
main = do
    res <- parseT parseStuff "abcdef"
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
    let pp = pureParsing "63553"
    case pp of
        Left err => putStrLn err
        Right xs => printLn xs
    pure ()