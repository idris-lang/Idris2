||| Is there a more common name for this transformer?
||| `ListT m a` is for `m (List a)` rather than this more progressive thing

module Libraries.Data.Tap

-- Note that `Tap m` is not strictly positive if `m` is not
%default covering

public export
data Tap : (Type -> Type) -> Type -> Type where
  Nil : Tap m a
  (::) : a -> m (Tap m a) -> Tap m a

export
Functor m => Functor (Tap m) where
  map f = \case
    [] => []
    x :: mxs => f x :: map (map f) mxs

export
traverse : Monad m => (a -> m b) -> Tap m a -> m (Tap m b)
traverse f [] = pure []
traverse f (x :: mxs) = pure (!(f x) :: (mxs >>= traverse f))

export
filter : Monad m => (a -> Bool) -> Tap m a -> m (Tap m a)
filter p [] = pure []
filter p (x :: mxs)
  = do let mxs = mxs >>= filter p
       if p x
         then pure $ x :: mxs
         else mxs
