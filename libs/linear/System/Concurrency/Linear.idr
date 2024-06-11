module System.Concurrency.Linear

import Control.Linear.LIO
import System.Concurrency

||| Run two linear computations in parallel and return the results.
export
par1 : L1 IO a -@ L1 IO b -@ L1 IO (LPair a b)
par1 x y
  = do aChan <- makeChannel
       bChan <- makeChannel
       aId <- liftIO1 $ fork $ withChannel aChan x
       bId <- liftIO1 $ fork $ withChannel bChan y
       a <- channelGet aChan
       b <- channelGet bChan
       pure1 (a # b)

  where

  -- This unsafe implementation temporarily bypasses the linearity checker.
  -- However `par`'s implementation does not duplicate the values
  -- and the type of `par` ensures that client code is not allowed to either!
  withChannel : Channel t -> L1 IO t -@ IO ()
  withChannel ch = assert_linear $ \ act => do
    a <- LIO.run (act >>= assert_linear pure)
    channelPut ch a

||| Run two unrestricted computations in parallel and return the results.
export
par : L IO a -@ L IO b -@ L IO (a, b)
par x y = do
  (MkBang a # MkBang b) <- par1 (bang x) (bang y)
  pure (a, b)
