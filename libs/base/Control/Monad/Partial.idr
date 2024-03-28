module Control.Monad.Partial

import Data.Nat

%default total


||| Delay/partiality monad. Represents partial computations which may not
||| terminate or cover all inputs. This can be preferable to defining a partial
||| Idris function as it allows termination to be proven as an external proof.
public export
data Partial : Type -> Type where
    Now : a -> Partial a
    Later : Inf (Partial a) -> Partial a


public export
Functor Partial where
    map f (Now x) = Now (f x)
    map f (Later x) = Later (map f x)


public export
Applicative Partial where
    pure = Now

    Now f <*> x = map f x
    Later f <*> x = Later (f <*> x)


public export
Monad Partial where
    Now x >>= f = f x
    Later x >>= f = Later (x >>= f)


||| A partial computation which never terminates (aka. undefined/bottom).
public export
never : Partial a
never = Later never


public export
data Total : Partial a -> Type where
    TNow : (x : a) -> Total (Now x)
    TLater : Total (Force x) -> Total (Later x)


||| Extract the value from a partial computation if you have a proof it is
||| actually total.
public export
runPartial : {x : Partial a} -> (0 _ : Total x) -> a
runPartial (TNow x) = x
runPartial (TLater t) = runPartial t
