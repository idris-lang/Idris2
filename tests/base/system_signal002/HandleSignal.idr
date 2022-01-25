import System.Signal
import System

main : IO ()
main = do
  Right () <- collectSignal SigABRT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  putStrLn "before"
  Right () <- raiseSignal SigABRT
    | Left (Error code) => putStrLn $ "got non-zero exit from system call: " ++ (show code)
  sleep 1
  Just SigABRT <- handleNextCollectedSignal
    | Just _  => putStrLn "received the wrong signal."
    | Nothing => putStrLn "did not receive expected signal."
  putStrLn "after"
  Right () <- defaultSignal SigABRT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  putStrLn "done."
