||| Utilities for dealing with %nomangle functions
module Compiler.NoMangle

import Core.Core
import Core.Context
import Libraries.Data.NameMap
import Libraries.Data.NameMap.Traversable

export
record NoMangleMap where
    constructor MkNMMap
    map : NameMap (Maybe String)

findNoMangle : List DefFlag -> Maybe NoMangleDirective
findNoMangle [] = Nothing
findNoMangle (NoMangle x :: _) = Just x
findNoMangle (_ :: xs) = findNoMangle xs

||| Get a map of all %nomangle names
||| Errors for all invalid names, so the backend can skip checking
||| or adding escape characters.
||| @ backend what backend is this being used in?
||| @ valid a validator to check a name is valid
|||         for the given backend
export
initNoMangle :
    {auto d : Ref Ctxt Defs} ->
    (backend : String) ->
    (valid : String -> Bool) ->
    Core (Ref NoMangleMap NoMangleMap)
initNoMangle backend valid = do
    defs <- get Ctxt
    let ctxt = defs.gamma
    map <- traverseNameMap
        (\nm, res => do
            Just gdef <- lookupCtxtExact (Resolved res) ctxt
                | Nothing => pure Nothing
            let Just ns = findNoMangle gdef.flags
                | Nothing => pure Nothing
            name <- case ns of
                CommonName name => pure name
                BackendNames ns =>
                    maybe
                        (throw (InternalError "missing %nomangle name for \{show nm} on \{backend} backend"))
                        pure
                        (lookupBackend ns)
            let True = valid name
                | False => throw (InternalError "\{show name} is not a valid name on the \{backend} backend")
            pure $ Just name
        ) ctxt.resolvedAs
    newRef NoMangleMap $ MkNMMap map
  where
    lookupBackend : List (String, String) -> Maybe String
    lookupBackend [] = Nothing
    lookupBackend ((b, n) :: ns) = if b == backend then Just n else lookupBackend ns

export
isNoMangle : NoMangleMap -> Name -> Maybe String
isNoMangle nm n = join $ lookup n nm.map

export
lookupNoMangle :
    {auto nm : Ref NoMangleMap NoMangleMap} ->
    Name ->
    Core (Maybe String)
lookupNoMangle n = pure $ isNoMangle !(get NoMangleMap) n

export
getAllNoMangle : {auto c : Ref Ctxt Defs} -> Core (List Name)
getAllNoMangle = do
    defs <- get Ctxt
    foldlNames (addNames defs) (pure []) defs.gamma.resolvedAs
  where
    addNames : Defs -> Core (List Name) -> Name -> Int -> Core (List Name)
    addNames defs acc _ res = do
        Just gdef <- lookupCtxtExact (Resolved res) defs.gamma
            | Nothing => acc
        let Just name = findNoMangle gdef.flags
            | Nothing => acc
        ns <- acc
        pure $ (Resolved res) :: ns
