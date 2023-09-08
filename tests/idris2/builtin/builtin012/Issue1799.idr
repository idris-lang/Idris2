module Main

import Data.Fin

%builtin Natural Nat
%builtin Natural Fin

%builtin NaturalToInteger Data.Fin.finToInteger

main : IO ()
main = putStrLn $ show $ finToInteger $ FS $ FZ {k=34}
