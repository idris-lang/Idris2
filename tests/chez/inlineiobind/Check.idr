import Data.List
import Data.String
import System.File

path : String
path = "build/exec/main_app/main.ss"

mainLine : String -> Bool
mainLine str =
  ("(define Main-main" `isPrefixOf` str) &&
  ("prim__putStr" `isInfixOf` str) &&
  not ("io_bind" `isInfixOf` str)

main : IO ()
main = do
  Right str <- readFile path
    | Left err => putStrLn "Error when reading \{path}"
  case any mainLine (lines str) of
    True  => putStrLn "io_bind correctly inlined"
    False => putStrLn "Failed to inline io_bind"
