||| State used during JS code generation and when
||| converting `NamedCExp` to imperative statements.
module Compiler.ES.State

import Core.Context
import Compiler.ES.Ast
import Compiler.NoMangle
import Libraries.Data.SortedMap
import Libraries.Data.SortedSet
import Libraries.Data.SortedSet as SortedSet
import Core.Name.Namespace as Core.Name.Namespace
import Core.Name as Core.Name

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
data EsCGMode = Pretty | Compact | Minimal

||| We only keep user defined local names and only so
||| in `Pretty` mode.
export
keepLocalName : Name -> EsCGMode -> Bool
keepLocalName (UN n) Pretty = True
keepLocalName _      _      = False

||| We mangle toplevel function names only in `Minimal` mode.
export
keepRefName : Name -> EsCGMode -> Bool
keepRefName _ Minimal = False
keepRefName _ _       = True

--------------------------------------------------------------------------------
--          Foreign Imports
--------------------------------------------------------------------------------

public export
data EsForeignBackend = EsForeignBackend_Node | EsForeignBackend_Browser | EsForeignBackend_Javascript

public export
Eq EsForeignBackend where
  (EsForeignBackend_Node) == (EsForeignBackend_Node) = True
  (EsForeignBackend_Browser) == (EsForeignBackend_Browser) = True
  (EsForeignBackend_Javascript) == (EsForeignBackend_Javascript) = True
  _ == _ = False

public export
Show EsForeignBackend where
  show EsForeignBackend_Node = "EsForeignBackend_Node"
  show EsForeignBackend_Browser = "EsForeignBackend_Browser"
  show EsForeignBackend_Javascript = "EsForeignBackend_Javascript"

public export
Ord EsForeignBackend where
  compare EsForeignBackend_Node EsForeignBackend_Node = EQ
  compare EsForeignBackend_Browser EsForeignBackend_Browser = EQ
  compare EsForeignBackend_Javascript EsForeignBackend_Javascript = EQ
  compare EsForeignBackend_Node EsForeignBackend_Browser = LT
  compare EsForeignBackend_Node EsForeignBackend_Javascript = LT
  compare EsForeignBackend_Browser EsForeignBackend_Javascript = LT
  compare _ _ = GT

public export
esForeignBackend__toString : EsForeignBackend -> String
esForeignBackend__toString EsForeignBackend_Node = "node"
esForeignBackend__toString EsForeignBackend_Browser = "browser"
esForeignBackend__toString EsForeignBackend_Javascript = "javascript"

public export
esForeignBackend__toDir : EsForeignBackend -> String
esForeignBackend__toDir EsForeignBackend_Node = "node"
esForeignBackend__toDir EsForeignBackend_Browser = "browser"
esForeignBackend__toDir EsForeignBackend_Javascript = "js"

public export
esForeignBackend__fromString : String -> Maybe EsForeignBackend
esForeignBackend__fromString "node" = Just EsForeignBackend_Node
esForeignBackend__fromString "browser" = Just EsForeignBackend_Browser
esForeignBackend__fromString "javascript" = Just EsForeignBackend_Javascript
esForeignBackend__fromString _ = Nothing

||| Code compiler backend?
public export
data ESSupportedBackendOrFallback = NodePreferredJavascriptFallback | BrowserPreferredJavascriptFallback

public export
Show ESSupportedBackendOrFallback where
  show NodePreferredJavascriptFallback    = "NodePreferredJavascriptFallback"
  show BrowserPreferredJavascriptFallback = "BrowserPreferredJavascriptFallback"

public export
eSSupportedBackend__toListBackends : ESSupportedBackendOrFallback -> List EsForeignBackend
eSSupportedBackend__toListBackends NodePreferredJavascriptFallback = [EsForeignBackend_Node,EsForeignBackend_Javascript]
eSSupportedBackend__toListBackends BrowserPreferredJavascriptFallback = [EsForeignBackend_Browser,EsForeignBackend_Javascript]

public export
eSSupportedBackend__toPrimaryBackend : ESSupportedBackendOrFallback -> EsForeignBackend
eSSupportedBackend__toPrimaryBackend NodePreferredJavascriptFallback = EsForeignBackend_Node
eSSupportedBackend__toPrimaryBackend BrowserPreferredJavascriptFallback = EsForeignBackend_Browser

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
  mode     : EsCGMode

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
  preamble : SortedMap (EsForeignBackend {- dir -}, String {- file -}) (SortedSet (String {- js func name -}, String {- import as -}))

  ||| Accepted codegen types in foreign function definitions.
  ||| For JS, this is either `["node","javascript"]` or
  ||| `["browser","javascript"]`.
  supportedBackendPrimaryAndFallback : ESSupportedBackendOrFallback

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

updatePreamble :  {auto c : Ref ESs ESSt}
               -> (
                   SortedMap (EsForeignBackend {- dir -}, String {- file -}) (SortedSet (String {- js func name -}, String {- import as -}))
                 -> Either (List String) (SortedMap (EsForeignBackend {- dir -}, String {- file -}) (SortedSet (String {- js func name -}, String {- import as -})))
                )
               -> Core ()
updatePreamble updateOrError = do
  esState <- get ESs
  let preamble' = preamble esState
  case updateOrError preamble' of
    Left err => errorConcat err
    Right newPreamble => put ESs $ { preamble := newPreamble } esState


||| Add a new set of definitions under the given name to
||| the preamble. Fails with an error if a different set
||| of definitions have already been added under the same name.
export
addToImportFileToPreamble :  {auto c : Ref ESs ESSt}
                          -> (EsForeignBackend {- dir -}, String {- file -})
                          -> (String {- js func name -}, String {- import as -})
                          -> Core ()
addToImportFileToPreamble (backend, fileName) (jsFunctionNameString_fromJsFile, jsFunctionNameString_importedAs) = do
  updatePreamble $ \preamble' =>
    case lookup (backend, fileName) preamble' of
      Nothing => Right $ insert (backend, fileName) (SortedSet.singleton (jsFunctionNameString_fromJsFile, jsFunctionNameString_importedAs)) preamble'
      Just idrisFunctionsSet =>
        if SortedSet.contains (jsFunctionNameString_fromJsFile, jsFunctionNameString_importedAs) idrisFunctionsSet
          then Left
            [ "For file ", esForeignBackend__toDir backend, "/", fileName, ".js: ", jsFunctionNameString_fromJsFile, " was already imported"
            ]
          else
            Right $ insert (backend, fileName) (SortedSet.insert (jsFunctionNameString_fromJsFile, jsFunctionNameString_importedAs) idrisFunctionsSet) preamble'

--------------------------------------------------------------------------------
--          Initialize State
--------------------------------------------------------------------------------

||| Initial state of the code generator
export
init :  (mode  : EsCGMode)
     -> (isArg : Exp -> Bool)
     -> (isFun : Exp -> Bool)
     -> (backendOrFallback : ESSupportedBackendOrFallback)
     -> (noMangle : NoMangleMap)
     -> ESSt
init mode isArg isFun ccSupportedBackend noMangle =
  MkESSt mode isArg isFun 0 0 empty empty empty ccSupportedBackend noMangle

||| Reset the local state before defining a new toplevel
||| function.
export
reset : {auto c : Ref ESs ESSt} -> Core ()
reset = update ESs $ { loc := 0, locals := empty }
