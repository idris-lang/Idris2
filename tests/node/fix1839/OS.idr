import System.Info

main : IO ()
main = printLn (os /= "")
