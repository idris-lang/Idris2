import System.Signal
import System

main : IO ()
main = do
  Right () <- ignoreSignal SigABRT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  putStrLn "before"
  Right () <- raiseSignal SigABRT
    | Left (Error code) => putStrLn $ "received error code from signal call: " ++ (show code)
  sleep 1
  putStrLn "after"
  Right () <- defaultSignal SigABRT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  putStrLn "done."
