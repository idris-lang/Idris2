module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

import public Control.Monad.Trans

%default total

----------------------------------
--- Elaboration data structure ---
----------------------------------

public export
data LookupDir =
  ||| The dir of the `ipkg`-file, or the current dir if there is no one
  ProjectDir |
  ||| The source dir set in the `ipkg`-file, or the current dir if there is no one
  SourceDir |
  ||| The dir where the current module is located
  |||
  ||| For the module `Language.Reflection` it would be `<source_dir>/Language/`
  CurrentModuleDir |
  ||| The dir where submodules of the current module are located
  |||
  ||| For the module `Language.Reflection` it would be `<source_dir>/Language/Reflection/`
  SubmodulesDir |
  ||| The dir where built files are located, set in the `ipkg`-file and defaulted to `build`
  BuildDir

||| Elaboration scripts
||| Where types/terms are returned, binders will have unique, if not
||| necessarily human readabe, names
export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Map  : (a -> b) -> Elab a -> Elab b
     Ap   : Elab (a -> b) -> Elab a -> Elab b
     Bind : Elab a -> (a -> Elab b) -> Elab b
     Fail : FC -> String -> Elab a
     Warn : FC -> String -> Elab ()

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
     -- Get the visibility associated with a name
     GetVis : Name -> Elab (List (Name, Visibility))
     -- Get the type of a local variable
     GetLocalType : Name -> Elab TTImp
     -- Get the constructors of a data type. The name must be fully resolved.
     GetCons : Name -> Elab (List Name)
     -- Get all function definition names referred in a definition. The name must be fully resolved.
     GetReferredFns : Name -> Elab (List Name)
     -- Get the name of the current and outer functions, if it is applicable
     GetCurrentFn : Elab (SnocList Name)
     -- Check a group of top level declarations
     Declare : List Decl -> Elab ()

     -- Read the contents of a file, if it is present
     ReadFile : LookupDir -> (path : String) -> Elab $ Maybe String
     -- Writes to a file, replacing existing contents, if were present
     WriteFile : LookupDir -> (path : String) -> (contents : String) -> Elab ()
     -- Returns the specified type of dir related to the current idris project
     IdrisDir : LookupDir -> Elab String

export
Functor Elab where
  map = Map

export
Applicative Elab where
  pure = Pure
  (<*>) = Ap

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

  ||| Report a warning in elaboration at some location
  warnAt : FC -> String -> m ()

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

  ||| Get the metadata associated with a name. Returns all matching names and their types
  getInfo : Name -> m (List (Name, NameInfo))

  ||| Get the visibility associated with a name. Returns all matching names and their visibilities
  getVis : Name -> m (List (Name, Visibility))

  ||| Get the type of a local variable
  getLocalType : Name -> m TTImp

  ||| Get the constructors of a fully qualified data type name
  getCons : Name -> m (List Name)

  ||| Get all the name of function definitions that a given definition refers to (transitively)
  getReferredFns : Name -> m (List Name)

  ||| Get the name of the current and outer functions, if we are in a function
  getCurrentFn : m (SnocList Name)

  ||| Make some top level declarations
  declare : List Decl -> m ()

  ||| Read the contents of a file, if it is present
  readFile : LookupDir -> (path : String) -> m $ Maybe String

  ||| Writes to a file, replacing existing contents, if were present
  writeFile : LookupDir -> (path : String) -> (contents : String) -> m ()

  ||| Returns the specified type of dir related to the current idris project
  idrisDir : LookupDir -> m String

export %inline
||| Report an error in elaboration
fail : Elaboration m => String -> m a
fail = failAt EmptyFC

export %inline
||| Report an error in elaboration
warn : Elaboration m => String -> m ()
warn = warnAt EmptyFC

||| Log the current goal type, if the log level is >= the given level
export %inline
logGoal : Elaboration m => String -> Nat -> String -> m ()
logGoal str n msg = whenJust !goal $ logTerm str n msg

export
Elaboration Elab where
  failAt         = Fail
  warnAt         = Warn
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
  getVis         = GetVis
  getLocalType   = GetLocalType
  getCons        = GetCons
  getReferredFns = GetReferredFns
  getCurrentFn   = GetCurrentFn
  declare        = Declare
  readFile       = ReadFile
  writeFile      = WriteFile
  idrisDir       = IdrisDir

public export
Elaboration m => MonadTrans t => Monad (t m) => Elaboration (t m) where
  failAt              = lift .: failAt
  warnAt              = lift .: warnAt
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
  getVis              = lift . getVis
  getLocalType        = lift . getLocalType
  getCons             = lift . getCons
  getReferredFns      = lift . getReferredFns
  getCurrentFn        = lift getCurrentFn
  declare             = lift . declare
  readFile            = lift .: readFile
  writeFile d         = lift .: writeFile d
  idrisDir            = lift . idrisDir

||| Catch failures and use the `Maybe` monad instead
export
catch : Elaboration m => Elab a -> m (Maybe a)
catch elab = try (Just <$> elab) (pure Nothing)

||| Run proof search to attempt to find a value of the input type.
||| Useful to check whether a give interface constraint is satisfied.
export
search : Elaboration m => (0 ty : Type) -> m (Maybe ty)
search ty = catch $ check {expected = ty} `(%search)
