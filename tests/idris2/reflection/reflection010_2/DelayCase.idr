module Main

import Language.Reflection

%language ElabReflection
%logging 1

forceDelay : Lazy Int -> Unit
forceDelay = \(Delay x) => ()

test : Elab ()
test = do
  q <- quote forceDelay
  logTerm "" 1 "forceDelay" q
  f <- check {expected=Lazy Int -> Unit} q
  logMsg "" 1 "delay case round-trip"
  pure ()

%runElab test
