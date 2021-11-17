import Data.String.Parser

main : IO ()
main = do
    let res = parse (satisfy isDigit) "100"
    printLn res
