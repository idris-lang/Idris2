module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

-- Elaboration scripts. Where types/terms are returned, binders will have
-- unique, if not necessarily human readabe, names
export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b
     Fail : String -> Elab a

     LogMsg : Nat -> String -> Elab ()
     LogTerm : Nat -> String -> TTImp -> Elab ()

     -- Elaborate a TTImp term to a concrete value
     Check : {expected : Type} -> TTImp -> Elab expected
     -- Quote a concrete expression back to a TTImp
     Quote : val -> Elab TTImp

     -- Elaborate under a lambda
     Lambda : (0 x : Type) ->
              {0 ty : x -> Type} ->
              ((val : x) -> Elab (ty val)) -> Elab ((val : x) -> (ty val))

     -- Get the current goal type, if known 
     -- (it might need to be inferred from the solution)
     Goal : Elab (Maybe TTImp)
     -- Get the names of local variables in scope
     LocalVars : Elab (List Name)
     -- Generate a new unique name, based on the given string
     GenSym : String -> Elab Name
     -- Put a name in the current namespace
     InCurrentNS : Name -> Elab Name
     -- Get the types of every name which matches.
     -- There may be ambiguities - returns a list of fully explicit names
     -- and their types. If there's no results, the name is undefined.
     GetType : Name -> Elab (List (Name, TTImp))
     -- Get the type of a local variable
     GetLocalType : Name -> Elab TTImp
     -- Get the constructors of a data type. The name must be fully resolved.
     GetCons : Name -> Elab (List Name)
     -- Check a group of top level declarations
     Declare : List Decl -> Elab ()

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
fail : String -> Elab a
fail = Fail

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

export
check : {expected : Type} -> TTImp -> Elab expected
check = Check

export
quote : val -> Elab TTImp
quote = Quote

export
lambda : (0 x : Type) ->
         {0 ty : x -> Type} ->
         ((val : x) -> Elab (ty val)) -> Elab ((val : x) -> (ty val))
lambda = Lambda

export
goal : Elab (Maybe TTImp)
goal = Goal

export
localVars : Elab (List Name)
localVars = LocalVars

export
genSym : String -> Elab Name
genSym = GenSym

export
inCurrentNS : Name -> Elab Name
inCurrentNS = InCurrentNS

export
getType : Name -> Elab (List (Name, TTImp))
getType = GetType

export
getLocalType : Name -> Elab TTImp
getLocalType = GetLocalType

export
getCons : Name -> Elab (List Name)
getCons = GetCons

export
declare : List Decl -> Elab ()
declare = Declare
