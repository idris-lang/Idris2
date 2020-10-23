module Constant

import System.Concurrency

constant : IO ()
constant = do
  let a = await $ fork "String"
  putStrLn a
