
import Data.Fin

autobind infixr 0 `bind`

bind : Monad m => m a -> (a -> m b) -> m b
bind = (>>=)

both : Maybe (Nat, Nat) -> Maybe Nat
both m = (MkPair x y := m) `bind` Just (x + y)
