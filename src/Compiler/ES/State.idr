||| State used during JS code generation and when
||| converting `NamedCExp` to imperative statements.
module Compiler.ES.State

import Core.Context
import Compiler.ES.Ast
import Compiler.NoMangle
import Libraries.Data.SortedMap

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Convenient alias for `throw . InternalError`
export
error : String -> Core a
error = throw . InternalError

||| Convenient alias for `error . fastConcat`.
export
errorConcat : List String -> Core a
errorConcat = error . fastConcat

--------------------------------------------------------------------------------
--          CG Mode
--------------------------------------------------------------------------------

||| Specifies the readability of the generated code.
|||
||| In `Pretty` mode (the default), the codegen will
||| lift multiline lambdas from argument lists to the
||| surrounding scope and keep user generated names.
||| In addition, blocks of code are laid out with indentation
||| and linebreaks for better readability.
|||
||| In `Compact` mode, all local variables are replace with
||| short machine generated ones, and every toplevel
||| function is printed on a single line without
||| line-breaks or indentation.
|||
||| Finally, `Minimal` mode is like `Compact`, but toplevel
||| function names will be mangled and replaced with
||| machine generated indices.
public export
data CGMode = Pretty | Compact | Minimal

||| We only keep user defined local names and only so
||| in `Pretty` mode.
export
keepLocalName : Name -> CGMode -> Bool
keepLocalName (UN n) Pretty = True
keepLocalName _      _      = False

||| We mangle toplevel function names only in `Minimal` mode.
export
keepRefName : Name -> CGMode -> Bool
keepRefName _ Minimal = False
keepRefName _ _       = True

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

public export
data ESs : Type where

||| Settings and state used during JS code generation.
public export
record ESSt where
  constructor MkESSt
  ||| Whether to always use minimal names
  mode     : CGMode

  ||| Returns `True`, if the given expression can be used as an
  ||| argument in a function call. (If this returns `False`, the
  ||| given expression will be lifted to the surrounding scope
  ||| and bound to a new local variable).
  isArg    : Exp -> Bool

  ||| Returns `True`, if the given expression can be used directly
  ||| in a function application. (If this returns `False`, the
  ||| given expression will be lifted to the surrounding scope
  ||| and bound to a variable).
  isFun    : Exp -> Bool

  ||| Current local variable index
  loc      : Int

  ||| Current global variable index
  ref      : Int

  ||| Mapping from local names to minimal expressions
  locals   : SortedMap Name Minimal

  ||| Mapping from toplevel function names to variables
  refs     : SortedMap Name Var

  ||| Mappings from name to definitions to be added
  ||| to the preamble.
  preamble : SortedMap String String

  ||| Accepted codegen types in foreign function definitions.
  ||| For JS, this is either `["node","javascript"]` or
  ||| `["browser","javascript"]`.
  ccTypes  : List String

  ||| %nomangle names
  noMangleMap : NoMangleMap

--------------------------------------------------------------------------------
--          Local Variables
--------------------------------------------------------------------------------

||| Map a local name to the given minimal expression
export
addLocal : { auto c : Ref ESs ESSt } -> Name -> Minimal -> Core ()
addLocal n v = update ESs $ { locals $= insert n v }

||| Get and bump the local var index
export
nextLocal : { auto c : Ref ESs ESSt } -> Core Var
nextLocal = do
  st <- get ESs
  put ESs $ { loc $= (+1) } st
  pure $ VLoc st.loc

||| Register a `Name` as a local variable. The name is kept
||| unchanged if `keepLocalName` returns `True` with the
||| current name and state, otherwise it is converted to
||| a new local variable.
export
registerLocal : {auto c : Ref ESs ESSt} -> (name : Name) -> Core Var
registerLocal n = do
  st <- get ESs
  if keepLocalName n st.mode
     then let v = VName n in addLocal n (MVar v) >> pure v
     else do v <- nextLocal
             addLocal n (MVar v)
             pure v

||| Look up a name and call `registerLocal` in case it has
||| not been added to the map of local names.
export
getOrRegisterLocal : {auto c : Ref ESs ESSt} -> Name -> Core Minimal
getOrRegisterLocal n = do
  Nothing <- lookup n . locals <$> get ESs
    | Just v => pure v
  MVar <$> registerLocal n

||| Maps the given list of names (from a pattern match
||| on a data constructor) to the corresponding
||| projections on the given scrutinee.
export
projections :  {auto c : Ref ESs ESSt}
            -> (scrutinee : Minimal)
            -> List Name
            -> Core ()
projections sc xs =
  let ps = zip [1..length xs] xs
   in traverse_ (\(i,n) => addLocal n $ MProjection i sc) ps

--------------------------------------------------------------------------------
--          Toplevel Names
--------------------------------------------------------------------------------

||| Map a toplevel function name to the given `Var`
export
addRef : { auto c : Ref ESs ESSt } -> Name -> Var -> Core ()
addRef n v = update ESs $ { refs $= insert n v }

||| Get and bump the local ref index
export
nextRef : { auto c : Ref ESs ESSt } -> Core Var
nextRef = do
  st <- get ESs
  put ESs $ { ref $= (+1) } st
  pure $ VRef st.ref

registerRef :  {auto c : Ref ESs ESSt}
            -> (name : Name)
            -> Core Var
registerRef n = do
  st <- get ESs
  if keepRefName n st.mode || isJust (isNoMangle st.noMangleMap n)
     then let v = VName n in addRef n v >> pure v
     else do v <- nextRef
             addRef n v
             pure v

||| Look up a name and call `registerRef` in case it has
||| not been added to the map of toplevel function names.
||| The name will be replace with an index if the current
||| `GCMode` is set to `Minimal`.
export
getOrRegisterRef :  {auto c : Ref ESs ESSt}
                 -> Name
                 -> Core Var
getOrRegisterRef n = do
  Nothing <- lookup n . refs <$> get ESs
    | Just v => pure v
  registerRef n

--------------------------------------------------------------------------------
--          Preamble and Foreign Definitions
--------------------------------------------------------------------------------

||| Add a new set of definitions under the given name to
||| the preamble. Fails with an error if a different set
||| of definitions have already been added under the same name.
export
addToPreamble :  {auto c : Ref ESs ESSt}
              -> (name : String)
              -> (def : String) -> Core ()
addToPreamble name def = do
  s <- get ESs
  case lookup name (preamble s) of
    Nothing => put ESs $ { preamble $= insert name def } s
    Just x =>
      unless (x == def) $ do
        errorConcat
              [ "two incompatible definitions for ", name
              , "<|",x ,"|> <|" , def, "|>"
              ]

--------------------------------------------------------------------------------
--          Initialize State
--------------------------------------------------------------------------------

||| Initial state of the code generator
export
init :  (mode  : CGMode)
     -> (isArg : Exp -> Bool)
     -> (isFun : Exp -> Bool)
     -> (types : List String)
     -> (noMangle : NoMangleMap)
     -> ESSt
init mode isArg isFun ccs noMangle =
  MkESSt mode isArg isFun 0 0 empty empty empty ccs noMangle

||| Reset the local state before defining a new toplevel
||| function.
export
reset : {auto c : Ref ESs ESSt} -> Core ()
reset = update ESs $ { loc := 0, locals := empty }
