import Data.Fin
import Data.List1

hours : List (Fin 12)
hours = forget (allFins 11)

main : IO ()
main = do
    printLn hours

    printLn $ map finS hours
    printLn $ map complement hours

    printLn $ map (+ 3) hours
    printLn $ map (* 5) hours

    printLn $ map negate hours
    printLn $ map ((-) 3) hours
    printLn $ map (flip (-) 3) hours
