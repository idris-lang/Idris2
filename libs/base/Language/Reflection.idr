module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

import public Control.Monad.Trans

%default total

----------------------------------
--- Elaboration data structure ---
----------------------------------

||| Elaboration scripts
||| Where types/terms are returned, binders will have unique, if not
||| necessarily human readabe, names
export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b
     Fail : FC -> String -> Elab a

     Try : Elab a -> Elab a -> Elab a

     ||| Log a message. Takes a
     ||| * topic
     ||| * level
     ||| * message
     LogMsg : String -> Nat -> String -> Elab ()
     ||| Print and log a term. Takes a
     ||| * topic
     ||| * level
     ||| * message
     ||| * term
     LogTerm : String -> Nat -> String -> TTImp -> Elab ()
     ||| Resugar, print and log a term. Takes a
     ||| * topic
     ||| * level
     ||| * message
     ||| * term
     LogSugaredTerm : String -> Nat -> String -> TTImp -> Elab ()

     -- Elaborate a TTImp term to a concrete value
     Check : TTImp -> Elab expected
     -- Quote a concrete expression back to a TTImp
     Quote : (0 _ : val) -> Elab TTImp

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
     -- Get the metadata associated with a name
     GetInfo : Name -> Elab (List (Name, NameInfo))
     -- Get the type of a local variable
     GetLocalType : Name -> Elab TTImp
     -- Get the constructors of a data type. The name must be fully resolved.
     GetCons : Name -> Elab (List Name)
     -- Check a group of top level declarations
     Declare : List Decl -> Elab ()

export
Functor Elab where
  map f e = Bind e $ Pure . f

export
Applicative Elab where
  pure = Pure
  f <*> a = Bind f (<$> a)

export
Alternative Elab where
  empty = Fail EmptyFC ""
  l <|> r = Try l r

export
Monad Elab where
  (>>=) = Bind

-----------------------------
--- Elaboration interface ---
-----------------------------

public export
interface Monad m => Elaboration m where

  ||| Report an error in elaboration at some location
  failAt : FC -> String -> m a

  ||| Try the first elaborator. If it fails, reset the elaborator state and
  ||| run the second
  try : Elab a -> Elab a -> m a

  ||| Write a log message, if the log level is >= the given level
  logMsg : String -> Nat -> String -> m ()

  ||| Write a log message and a rendered term, if the log level is >= the given level
  logTerm : String -> Nat -> String -> TTImp -> m ()

  ||| Write a log message and a resugared & rendered term, if the log level is >= the given level
  logSugaredTerm : String -> Nat -> String -> TTImp -> m ()

  ||| Check that some TTImp syntax has the expected type
  ||| Returns the type checked value
  check : TTImp -> m expected

  ||| Return TTImp syntax of a given value
  quote : (0 _ : val) -> m TTImp

  ||| Build a lambda expression
  lambda : (0 x : Type) ->
           {0 ty : x -> Type} ->
           ((val : x) -> Elab (ty val)) -> m ((val : x) -> (ty val))

  ||| Get the goal type of the current elaboration
  |||
  ||| `Nothing` means the script is run in the top-level `%runElab` clause.
  ||| If elaboration script is run in expression mode, this function will always return `Just`.
  ||| In the case of unknown result type in the expression mode, returned `TTImp` would be an `IHole`.
  goal : m (Maybe TTImp)

  ||| Get the names of the local variables in scope
  localVars : m (List Name)

  ||| Generate a new unique name
  genSym : String -> m Name

  ||| Given a name, return the name decorated with the current namespace
  inCurrentNS : Name -> m Name

  ||| Given a possibly ambiguous name, get all the matching names and their types
  getType : Name -> m (List (Name, TTImp))

  ||| Get the metadata associated with a name. Returns all matching namea and their types
  getInfo : Name -> m (List (Name, NameInfo))

  ||| Get the type of a local variable
  getLocalType : Name -> m TTImp

  ||| Get the constructors of a fully qualified data type name
  getCons : Name -> m (List Name)

  ||| Make some top level declarations
  declare : List Decl -> m ()

export %inline
||| Report an error in elaboration
fail : Elaboration m => String -> m a
fail = failAt EmptyFC

||| Log the current goal type, if the log level is >= the given level
export %inline
logGoal : Elaboration m => String -> Nat -> String -> m ()
logGoal str n msg = whenJust !goal $ logTerm str n msg

export
Elaboration Elab where
  failAt         = Fail
  try            = Try
  logMsg         = LogMsg
  logTerm        = LogTerm
  logSugaredTerm = LogSugaredTerm
  check          = Check
  quote          = Quote
  lambda         = Lambda
  goal           = Goal
  localVars      = LocalVars
  genSym         = GenSym
  inCurrentNS    = InCurrentNS
  getType        = GetType
  getInfo        = GetInfo
  getLocalType   = GetLocalType
  getCons        = GetCons
  declare        = Declare

public export
Elaboration m => MonadTrans t => Monad (t m) => Elaboration (t m) where
  failAt              = lift .: failAt
  try                 = lift .: try
  logMsg s            = lift .: logMsg s
  logTerm s n         = lift .: logTerm s n
  logSugaredTerm s n  = lift .: logSugaredTerm s n
  check               = lift . check
  quote v             = lift $ quote v
  lambda x            = lift . lambda x
  goal                = lift goal
  localVars           = lift localVars
  genSym              = lift . genSym
  inCurrentNS         = lift . inCurrentNS
  getType             = lift . getType
  getInfo             = lift . getInfo
  getLocalType        = lift . getLocalType
  getCons             = lift . getCons
  declare             = lift . declare

||| Catch failures and use the `Maybe` monad instead
export
catch : Elaboration m => Elab a -> m (Maybe a)
catch elab = try (Just <$> elab) (pure Nothing)

||| Run proof search to attempt to find a value of the input type.
||| Useful to check whether a give interface constraint is satisfied.
export
search : Elaboration m => (ty : Type) -> m (Maybe ty)
search ty = catch $ check {expected = ty} `(%search)
