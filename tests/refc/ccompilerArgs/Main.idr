import System.FFI

libexternal : String -> String
libexternal fn = "C:" ++ fn ++ ",libexternalc,externalc.h"

%foreign (libexternal "add")
add : Int -> Int -> Int

%foreign (libexternal "fastfibsum")
fastfibsum : Int -> Int

main : IO ()
main = do
    printLn $ show (add 50 23)
    printLn $ show ([fastfibsum x | x <- [0..10]])