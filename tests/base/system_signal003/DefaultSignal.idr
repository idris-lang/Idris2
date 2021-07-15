import System.Signal
import System

main : IO ()
main = do
  Right () <- ignoreSignal SigABRT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  Right () <- defaultSignal SigABRT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  Right () <- raiseSignal SigABRT
    | Left (Error code) => putStrLn $ "received non-zero exit from system call: " ++ (show code)
  sleep 1
  putStrLn "(should not get here)."
