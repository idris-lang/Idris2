module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

public export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b
     Log : Nat -> String -> Elab ()

     -- Check a TTImp term against the current goal type
     Check : TTImp -> Elab TT

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
