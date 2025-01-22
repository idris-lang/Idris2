module System.Concurrency.Linear

import Control.Linear.LIO
import System.Concurrency

||| Run a linear computation in a separate thread
export
fork1 : L IO () -@ L IO ThreadID
fork1 act = liftIO1 $ fork $ LIO.run act

||| Run a computation concurrently to the current thread.
||| This returns a receiver for the value.
export
concurrently : L IO a -@ L1 IO (L IO a)
concurrently act = do
  ch <- makeChannel
  _ <- fork1 $ do
    x <- act
    channelPut ch x
  pure1 $ channelGet ch

||| Run a computation concurrently to the current thread.
||| This returns a receiver for the value. A typical usage
||| pattern is showcased by the implementation of `par1`:
||| in a do block start executing a series of actions
||| concurrently and then collect the results with a series
||| of receiving steps.
|||
|||  do recva <- concurrently1 ioa
|||     recvb <- concurrently1 iob
|||     a <- recva
|||     b <- recvb
|||     pure1 (a # b)
export
concurrently1 : L1 IO a -@ L1 IO (L1 IO a)
concurrently1 act = do
  ch <- makeChannel
  _ <- fork1 $ withChannel ch act
  pure1 $ do
    a <- channelGet ch
    pure1 a

  where

  -- This unsafe implementation temporarily bypasses the linearity checker.
  -- However `concurrently`'s implementation does not duplicate the values
  -- and the type of `concurrently` ensures that client code is not allowed
  -- to either!
  withChannel : Channel t -> L1 IO t -@ L IO ()
  withChannel ch = assert_linear $ \ act => do
    a <- act
    assert_linear (channelPut ch) a


||| Run two linear computations concurrently and return the results.
export
par1 : L1 IO a -@ L1 IO b -@ L1 IO (LPair a b)
par1 ioa iob
  = do -- run the two actions on separate threads
       recva <- concurrently1 ioa
       recvb <- concurrently1 iob
       -- collect the results
       a <- recva
       b <- recvb
       -- return the pair
       pure1 (a # b)

||| Run two unrestricted computations in parallel and return the results.
export
par : L IO a -@ L IO b -@ L IO (a, b)
par x y = do
  (MkBang a # MkBang b) <- par1 (bang x) (bang y)
  pure (a, b)
