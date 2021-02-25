module Issue758

-- introduce linear bind and linear pure
interface LMonad m where
  pure : (1 _ : a) -> m a
  (>>=) : (1 _ : m a) -> (1 _ : (1 _ : a) -> m b) -> m b

(>>) : LMonad m => (1 _ : m ()) -> (1 _ : m a) -> m a
ma >> mb = ma >>= \ () => mb

fail : LMonad m => (1 _ : m ((1 _ : a) -> b)) -> (1 _ : a) -> m b
fail ma a = do f <- ma
               ?what_is_f
               pure (f a)

