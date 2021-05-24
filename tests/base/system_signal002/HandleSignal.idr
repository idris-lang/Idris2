import System.Signal
import System

main : IO ()
main = do 
  Right () <- collectSignal SigQUIT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  pid <- getPID
  putStrLn "before"
  Right () <- sendSignal SigQUIT pid
    | Left (Error code) => putStrLn $ "got non-zero exit from system call: " ++ (show code)
  sleep 1
  Just SigQUIT <- handleNextCollectedSignal
    | Just _  => putStrLn "received the wrong signal."
    | Nothing => putStrLn "did not receive expected signal."
  putStrLn "after"
  Right () <- defaultSignal SigQUIT
    | Left (Error code) => putStrLn $ "error " ++ (show code)
  putStrLn "done."
