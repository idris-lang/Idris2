import Data.IORef
import System
import System.Clock
import System.File

-- Requests a garbage collection and waits for it. A collection needs every
-- thread that is running Scheme code to stop at a safe point.
%foreign "scheme,chez:collect-rendezvous"
prim__collect : PrimIO ()

msSince : Clock Monotonic -> IO Integer
msSince t0 = do
  t <- clockTime Monotonic
  let d = timeDifference t t0
  pure (seconds d * 1000 + nanoseconds d `div` 1000000)

-- Collect garbage for half a second. Returns `False` if the blocking call
-- finished first: then a collection had to wait for it.
collectWhile : Clock Monotonic -> IORef Bool -> IO Bool
collectWhile t0 done = do
  primIO prim__collect
  if !(readIORef done)
    then pure False
    else if !(msSince t0) >= 500
      then pure True
      else collectWhile t0 done

-- Each blocking call takes 3 seconds, much longer than `collectWhile`.
check : String -> IO () -> IO ()
check name blockingCall = do
  done <- newIORef False
  _ <- fork $ do blockingCall
                 writeIORef done True
  t0 <- clockTime Monotonic
  ok <- collectWhile t0 done
  putStrLn $ name ++ ": "
    ++ if ok then "other threads kept running"
             else "other threads waited for it"

main : IO ()
main = do
  check "sleep" (sleep 3)
  check "usleep" (usleep 3000000)
  check "system" (ignore $ system "sleep 3")
  check "pclose" $ do
    Right h <- popen "sleep 3" Read
      | Left err => putStrLn "popen failed: \{show err}"
    ignore $ pclose h
  check "popen2Wait" $ do
    Right p <- popen2 "sleep 3"
      | Left err => putStrLn "popen2 failed: \{show err}"
    ignore $ popen2Wait p
