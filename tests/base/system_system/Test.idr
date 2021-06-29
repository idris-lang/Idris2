import System

main : IO ()
main = do
  0 <- system "bash zero.sh"
    | r => do putStrLn ("expecting zero, got " ++ (show r))
              exitFailure
  -- `system` returns result of `waitpid` which is not trivial to decode
  let True = !(system "bash seventeen.sh") /= 0
    | False => putStrLn "expecting 17, got zero"
  pure ()
