module SearchWriter

import Control.Monad.Identity
import Control.Monad.Writer

monadWriterInstance : (Monoid a) => MonadWriter a (Writer a)
monadWriterInstance = %search
