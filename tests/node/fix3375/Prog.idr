module Prog

import Data.IORef

%default total

%inline
release : IORef Nat -> IO ()
release ref = pure ()

%inline
readAndRelease : IORef Nat -> IO Nat
readAndRelease ref = do
  v <- readIORef ref
  release ref
  pure v

setget : IORef Nat -> IORef Nat -> IO (Nat,Nat)
setget r1 r2 = do
  writeIORef r1 100
  x <- readAndRelease r1
  y <- readAndRelease r2
  pure (x,y)

%noinline
letNoReplace : Nat -> Nat
letNoReplace x = let z := x * x in z

%noinline
letReplace : Nat
letReplace = let z := 10 * 10 in z

%noinline
nestedLetNoReplace : Nat -> Nat
nestedLetNoReplace x =
  let z := x * x in let y := z in y

%noinline
nestedLetReplace : Nat
nestedLetReplace =
  let z := 10 * 10 in let y := z in y

main : IO ()
main = do
  r1 <- newIORef Z
  r2 <- newIORef Z
  p  <- setget r1 r2
  printLn p
  printLn (letNoReplace 10)
  printLn letReplace
  printLn (nestedLetNoReplace 10)
  printLn nestedLetReplace
