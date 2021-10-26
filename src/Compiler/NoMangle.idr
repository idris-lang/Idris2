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

export
initNoMangle :
    {auto d : Ref Ctxt Defs} ->
    Core (Ref NoMangleMap NoMangleMap)
initNoMangle = do
    defs <- get Ctxt
    let ctxt = defs.gamma
    map <- traverseNameMap
        (\nm, res => do
            Just gdef <- lookupCtxtExact (Resolved res) ctxt
                | Nothing => pure Nothing
            pure $ findNoMangle gdef.flags
        ) ctxt.resolvedAs
    newRef NoMangleMap $ MkNMMap map
  where
    findNoMangle : List DefFlag -> Maybe String
    findNoMangle [] = Nothing
    findNoMangle (NoMangle x :: _) = Just x
    findNoMangle (_ :: xs) = findNoMangle xs

export
isNoMangle : NoMangleMap -> Name -> Maybe String
isNoMangle nm n = join $ lookup n nm.map

export
isNoMangleC :
    {auto nm : Ref NoMangleMap NoMangleMap} ->
    Name ->
    Core (Maybe String)
isNoMangleC n = pure $ isNoMangle !(get NoMangleMap) n
