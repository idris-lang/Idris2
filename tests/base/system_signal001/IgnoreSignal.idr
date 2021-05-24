import System.Signal
import System

main : IO ()
main = do
  Right () <- ignoreSignal SigQUIT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  pid <- getPID
  putStrLn "before"
  Right () <- sendSignal SigQUIT pid
    | Left (Error code) => putStrLn $ "received error code from signal call: " ++ (show code)
  sleep 1
  putStrLn "after"
  Right () <- defaultSignal SigQUIT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  putStrLn "done."
