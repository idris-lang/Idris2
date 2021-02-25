module Main

import Language.Reflection

%language ElabReflection

-- A performance test - previously this was slowing down hugely due to
-- quoting back HNFs on >>=, and as the environment gets bigger, the
-- environment of holes gets bigger and bigger, so quoting can start to take
-- far too long
perftest : Elab ()
perftest = do
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 1 . show)) [[the Int 1..10]] -- minor difference
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 2 . show)) [[the Int 1..10]] -- minor difference
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 3 . show)) [[the Int 1..10]] -- minor difference
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 4 . show)) [[the Int 1..10]] -- minor difference
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 5 . show)) [[the Int 1..10]] -- minor difference
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 6 . show)) [[the Int 1..10]] -- minor difference
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 7 . show)) [[the Int 1..10]] -- 0.3s
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 8 . show)) [[the Int 1..10]] -- 0.4s
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 9 . show)) [[the Int 1..10]] -- 0.5s
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 10 . show)) [[the Int 1..10]] -- 1.5s
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 11 . show)) [[the Int 1..10]] -- 4s
  logMsg "" 0 "Progress"
  traverse_ (traverse (logMsg "" 12 . show)) [[the Int 1..10]] -- 13s

%runElab perftest
