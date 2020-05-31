module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b
     LogMsg : Nat -> String -> Elab ()
     LogTerm : Nat -> String -> TTImp -> Elab ()

     -- Check a TTImp term against the current goal type
     Check : TTImp -> Elab TT
     -- Get the current goal type, if known 
     -- (it might need to be inferred from the solution)
     Goal : Elab (Maybe TTImp)

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

export
logMsg : Nat -> String -> Elab ()
logMsg = LogMsg

export
logTerm : Nat -> String -> TTImp -> Elab ()
logTerm = LogTerm

export
logGoal : Nat -> String -> Elab ()
logGoal n msg
    = do g <- Goal
         case g of
              Nothing => pure ()
              Just t => logTerm n msg t

-- Check a TTImp term against the current goal type
export
check : TTImp -> Elab TT
check = Check

export
goal : Elab (Maybe TTImp)
goal = Goal
