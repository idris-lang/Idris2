import Data.List
import Data.String
import System.File

path : String
path = "build/exec/enum_app/enum.ss"

mainLine : String -> Bool
mainLine str =
  ("(define Enum-main" `isPrefixOf` str) && (" 120 17))" `isInfixOf` str)

main : IO ()
main = do
  Right str <- readFile path
    | Left err => putStrLn "Error when reading \{path}"
  case any mainLine (lines str) of
    True  => putStrLn "Enum conversion optimized away"
    False => putStrLn "Failed to optimize away enum conversion"
