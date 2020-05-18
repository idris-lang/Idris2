module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

public export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b

     Check : TTImp -> Elab a

mutual
  export
  Functor Elab where
    map f e = do e' <- e
                 pure (f e')

  export
  Applicative Elab where
    pure = Pure
    f <*> a = do f' <- f
                 a' <- a
                 pure (f' a')

  export
  Monad Elab where
    (>>=) = Bind
