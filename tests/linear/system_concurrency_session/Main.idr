import Control.Linear.LIO
import System.Concurrency.Session

main : IO ()
main = LIO.run $ do
  let nm1 : String := "natrando"
  let nm2 : String := "computer"
  putStrLn "main: Forking two threads \{nm1} and \{nm2}"
  res <- fork (Send Nat $ Send Nat $ Recv Nat End)
    (\ ch => do let m : Nat := 100
                putStrLn "\{nm1}: picked the natural \{show m}"
                ch <- send ch m
                let n : Nat := 50
                putStrLn "\{nm1}: picked the natural \{show n}"
                ch <- send ch n
                (s # ch) <- recv ch
                end ch
                pure (m, n))
    (\ ch => do (m # ch) <- recv ch
                (n # ch) <- recv ch
                putStrLn "\{nm2}: summing \{show m} and \{show n}"
                let s = m + n
                ch <- send ch s
                end ch
                pure s)
  let mn = fst res
  let mplusn = snd res
  putStrLn {io = L IO} "main: Threads have finished and returned \{show mn} and \{show mplusn}"
