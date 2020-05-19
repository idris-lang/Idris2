import System.REPL

sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs tot inp
  = let val = cast inp in
        if val < 0
           then Nothing
           else let newVal = tot + val in
                    Just ("Subtotal: " ++ show newVal ++ "\n", newVal)

main : IO ()
main = replWith 0 "Value: " sumInputs
