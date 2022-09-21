||| Utilities for dealing with %nomangle functions
module Compiler.NoMangle

import Core.Core
import Core.Context
import Data.List
import Libraries.Data.NameMap
import Libraries.Data.NameMap.Traversable

export
record NoMangleMap where
    constructor MkNMMap
    map : NameMap String

||| Get a map of all %export names
||| Errors for all invalid names, so the backend can skip checking
||| or adding escape characters.
||| @ backend what backend is this being used in?
||| @ valid a validator to check a name is valid
|||         for the given backend
export
initNoMangle :
    {auto d : Ref Ctxt Defs} ->
    (backends : List String) ->
    (valid : String -> Bool) ->
    Core (Ref NoMangleMap NoMangleMap)
initNoMangle backends valid = do
    defs <- get Ctxt
    map <- traverseNameMap
        (\name, exps => do
            let Just (backend, expName) = lookupBackend backends exps
                | Nothing => throw (GenericMsg EmptyFC """
                    No valid %export specifier for \{show name}
                      Supported backends: \{showSep ", " backends}
                      Given backends: \{showSep ", " (fst <$> exps)}
                    """)
            let True = valid expName
                | False => throw (GenericMsg EmptyFC "\"\{expName}\" is not a valid name on \{backend} backend")
            pure expName)
        defs.foreignExports
    newRef NoMangleMap $ MkNMMap map
  where
    lookupBackend : List String -> List (String, String) -> Maybe (String, String)
    lookupBackend [] exps = Nothing
    lookupBackend (b :: bs) exps =
        case lookup b exps of
            Just exp => Just (b, exp)
            Nothing => lookupBackend bs exps

export
isNoMangle : NoMangleMap -> Name -> Maybe String
isNoMangle nm n = lookup n nm.map

export
lookupNoMangle :
    {auto nm : Ref NoMangleMap NoMangleMap} ->
    Name ->
    Core (Maybe String)
lookupNoMangle n = pure $ isNoMangle !(get NoMangleMap) n
