
import Data.Fin

private autobind infixr 0 >>
private autobind infixr 0 >=

(>>) : Monad m => m a -> (a -> m b) -> m b
(>>) = (>>=)

(>=) : Monad m => m a -> (a -> m b) -> m b
(>=) = (>>=)

both : Maybe (Nat, Nat) -> Maybe Nat
both m = (MkPair x y := m) >>= Just (x + y)
