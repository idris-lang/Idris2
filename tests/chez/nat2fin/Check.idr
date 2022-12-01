import Data.List
import Data.String
import System.File

path : String
path = "build/exec/test_app/test.ss"

mainLine : String -> Bool
mainLine str =
  ("(define Main-main" `isPrefixOf` str) && (" 375)" `isInfixOf` str)

main : IO ()
main = do
  Right str <- readFile path
    | Left err => putStrLn "Error when reading \{path}"
  case any mainLine (lines str) of
    True  => putStrLn "natToFinLt optimized away"
    False => putStrLn "failed to optimize away natToFinLt"
