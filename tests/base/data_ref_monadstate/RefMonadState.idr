module RefMonadState

import Control.Monad.State.Interface

import Data.Ref

%default total

fancy : MonadState Nat m => HasIO m => m String
fancy = do
  n <- get
  putStrLn "current n: \{show n}"
  put $ 20 + n
  pure "`\{show n}`"

main : IO ()
main = do
  ref <- newRef 18
  for_ [1..4] $ const $ fancy @{ForRef ref}
  putStrLn "resulting value: \{show !(readRef ref)}"
