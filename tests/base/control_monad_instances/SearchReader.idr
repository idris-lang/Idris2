module SearchReader

import Control.Monad.Identity
import Control.Monad.Reader

monadReaderInstance : MonadReader a (Reader a)
monadReaderInstance = %search
