module Control.Monad.Partial

%default total


||| Delay/partiality monad. Represents partial computations which may not
||| terminate or cover all inputs. This can be preferable to defining a partial
||| Idris function as it allows termination to be proven as an external proof.
data Partial : Type -> Type where
    Now : a -> Partial a
    Later : Inf (Partial a) -> Partial a


Functor Partial where
    map f (Now x) = Now (f x)
    map f (Later x) = Later (map f x)


Applicative Partial where
    pure = Now

    Now f <*> x = map f x
    Later f <*> x = Later (f <*> x)


Monad Partial where
    Now x >>= f = f x
    Later x >>= f = Later (x >>= f)


||| A partial computation which never terminates (aka. undefined/bottom)
never : Partial a
never = Later never
