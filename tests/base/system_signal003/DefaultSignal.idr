import System.Signal
import System

main : IO ()
main = do
  Right () <- ignoreSignal SigQUIT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  Right () <- defaultSignal SigQUIT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  pid <- getPID
  Right () <- sendSignal SigQUIT pid
    | Left (Error code) => putStrLn $ "received non-zero exit from system call: " ++ (show code)
  sleep 1
  putStrLn "(should not get here)."
