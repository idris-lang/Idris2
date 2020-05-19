import Control.Monad.State

increment : Nat -> State Nat ()
increment inc = do current <- get
                   put (current + inc)

