import System
import System.Info

main : IO ()
main = do
  0 <- system "bash zero.sh"
    | r => do putStrLn ("expecting zero, got " ++ (show r))
              exitFailure
  -- `system` returns result of `waitpid` which is not trivial to decode
  let True = !(System.system "bash seventeen.sh") /= 0
    | False => putStrLn "expecting 17, got zero"

  let nastyStr = "Hello \"world\" $PATH %PATH% \\\" `echo 'Uh, oh'`"
  ignore $ system $ "echo " ++ escapeArg nastyStr
  ignore $ system ["echo", nastyStr]

  if not isWindows
     then do ignore $ system $ "echo " ++ escapeArg "Hello\nworld"
             ignore $ system ["echo", "Hello\nworld"]
     else do putStrLn "Hello\nworld\nHello\nworld" -- Windows has no way of escaping '\n', so skip test
