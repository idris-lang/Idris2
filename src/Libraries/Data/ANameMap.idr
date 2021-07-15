-- like name map, but able to return ambiguous names
module Libraries.Data.ANameMap

import Core.Name

import Data.List
import Libraries.Data.NameMap
import Libraries.Data.StringMap

%default total

export
record ANameMap a where
     constructor MkANameMap
     -- for looking up by exact (completely qualified) names
     exactNames : NameMap a
     -- for looking up by name root or partially qualified (so possibly
     -- ambiguous) names. This doesn't store machine generated names.
     hierarchy : StringMap (List (Name, a))

export
empty : ANameMap a
empty = MkANameMap empty empty

||| Given a Name, and an ANameMap, look up that name exactly
export
lookupExact : Name -> ANameMap a -> Maybe a
lookupExact n dict = lookup n (exactNames dict)

export
lookupName : Name -> ANameMap a -> List (Name, a)
lookupName n dict
    = case userNameRoot n of
           Nothing => case lookupExact n dict of
                           Nothing => []
                           Just res => [(n, res)]
           Just r => case lookup r (hierarchy dict) of
                          Nothing => []
                          Just ns => filter (matches n . fst) ns

addToHier : Name -> a ->
            StringMap (List (Name, a)) -> StringMap (List (Name, a))
addToHier n val hier
     -- Only add user defined names. Machine generated names can only be
     -- found with the exactNames
     = case userNameRoot n of
            Nothing => hier
            Just root =>
                 case lookup root hier of
                      Nothing => insert root [(n, val)] hier
                      Just ns => insert root (update val ns) hier
  where
    update : a -> List (Name, a) -> List (Name, a)
    update val [] = [(n, val)]
    update val (old :: xs)
      = if n == fst old
          then (n, val) :: xs
          else old :: update val xs

export
addName : Name -> a -> ANameMap a -> ANameMap a
addName n val (MkANameMap dict hier)
     = let dict' = insert n val dict
           hier' = addToHier n val hier in
           MkANameMap dict' hier'

export
toList : ANameMap a -> List (Name, a)
toList dict = toList (exactNames dict)

export
fromList : List (Name, a) -> ANameMap a
fromList = fromList' empty
  where
    fromList' : ANameMap a -> List (Name, a) -> ANameMap a
    fromList' acc [] = acc
    fromList' acc ((k, v) :: ns) = fromList' (addName k v acc) ns

-- Merge two contexts, with entries in the first overriding entries in
-- the second
export
merge : ANameMap a -> ANameMap a -> ANameMap a
merge (MkANameMap exact hier) ctxt
    = insertFrom (toList exact) ctxt
  where
    insertFrom : List (Name, a) -> ANameMap a -> ANameMap a
    insertFrom [] ctxt = ctxt
    insertFrom ((n, val) :: cs) ctxt
        = insertFrom cs (addName n val ctxt)
