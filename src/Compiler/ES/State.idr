module Compiler.ES.State

import Core.Context
import Compiler.ES.Ast
import Libraries.Data.SortedMap

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

export
error : String -> Core a
error = throw . InternalError

export
errorConcat : List String -> Core a
errorConcat = error . concat

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
||| short machine generated one, and every toplevel
||| function is printed on a single line without
||| line-breaks and indentation.
|||
||| Finally, `Minimal` mode is like `Compact`, but toplevel
||| function names will be mangled and replaced with
||| machine generated indices.
public export
data CGMode = Pretty | Compact | Minimal

export
keepLocalName : Name -> CGMode -> Bool
keepLocalName (UN n) Pretty = True
keepLocalName _      _      = False

export
keepRefName : Name -> CGMode -> Bool
keepRefName _ Minimal = False
keepRefName _ _       = True

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

public export
data ESs : Type where

public export
record ESSt where
  constructor MkESSt
  ||| Whether to always use minimal names
  mode     : CGMode

  ||| Returns `True`, if the given expression can be used as an
  ||| argument in a function call. (If this returns `False`, the
  ||| given expression will be lifted to the surrounding scope
  ||| and bound to a variable).
  isArg    : Exp -> Bool

  ||| Returns `True`, if the given expression can be used directly
  ||| in a function application. (If this returns `False`, the
  ||| given expression will be lifted to the surrounding scope
  ||| and bound to a variable).
  isFun    : Exp -> Bool

  ||| Actual local variable index
  loc      : Int

  ||| Actual local variable index
  ref      : Int

  ||| Mapping from local names to minimal expressions
  locals   : SortedMap Name Minimal

  ||| Mapping from toplevel function names to `Var`s
  refs     : SortedMap Name Var

  ||| Mappings from name to definition to be added
  ||| to the preamble.
  preamble : SortedMap String String
  ccTypes  : List String

--------------------------------------------------------------------------------
--          Local Variables
--------------------------------------------------------------------------------

||| Map a local name to the given minimal expression
export
addLocal : { auto c : Ref ESs ESSt } -> Name -> Minimal -> Core ()
addLocal n v = update ESs $ record { locals $= insert n v }

||| Get and bump the local var index
export
nextLocal : { auto c : Ref ESs ESSt } -> Core Var
nextLocal = do
  st <- get ESs
  put ESs $ record { loc $= (+1) } st
  pure $ VLoc st.loc

export
registerLocal : {auto c : Ref ESs ESSt} -> (name : Name) -> Core Var
registerLocal n = do
  st <- get ESs
  if keepLocalName n st.mode
     then let v = VName n in addLocal n (MVar v) >> pure v
     else do v <- nextLocal
             addLocal n (MVar v)
             pure v
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

||| Map a toplevel name to the given `Var`
export
addRef : { auto c : Ref ESs ESSt } -> Name -> Var -> Core ()
addRef n v = update ESs $ record { refs $= insert n v }

||| Get and bump the local ref index
export
nextRef : { auto c : Ref ESs ESSt } -> Core Var
nextRef = do
  st <- get ESs
  put ESs $ record { ref $= (+1) } st
  pure $ VRef st.ref

registerRef : {auto c : Ref ESs ESSt} -> (name : Name) -> Core Var
registerRef n = do
  st <- get ESs
  if keepRefName n st.mode
     then let v = VName n in addRef n v >> pure v
     else do v <- nextRef
             addRef n v
             pure v
export
getOrRegisterRef : {auto c : Ref ESs ESSt} -> Name -> Core Var
getOrRegisterRef n = do
  Nothing <- lookup n . refs <$> get ESs
    | Just v => pure v
  registerRef n

--------------------------------------------------------------------------------
--          Preamble and Foreign Definitions
--------------------------------------------------------------------------------

export
addToPreamble : {auto c : Ref ESs ESSt} -> String -> String -> Core ()
addToPreamble name def = do
  s <- get ESs
  case lookup name (preamble s) of
    Nothing => put ESs $ record { preamble $= insert name def } s
    Just x =>
      if x == def
       then pure ()
       else errorConcat
              [ "two incompatible definitions for ", name
              , "<|",x ,"|> <|" , def, "|>"
              ]

--------------------------------------------------------------------------------
--          Initialize State
--------------------------------------------------------------------------------

||| Initial state of the code generator
export
init :  (mode : CGMode)
     -> (isArg : Exp -> Bool)
     -> (isFun : Exp -> Bool)
     -> (types : List String)
     -> ESSt
init mode isArg isFun ccs =
  MkESSt mode isArg isFun 0 0 empty empty empty ccs

export
reset : {auto c : Ref ESs ESSt} -> Core ()
reset = update ESs $ record { loc = 0, locals = empty }
