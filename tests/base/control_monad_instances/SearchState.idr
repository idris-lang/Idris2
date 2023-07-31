module SearchState

import Control.Monad.State

monadWriterInstance : MonadState a (State a)
monadWriterInstance = %search
