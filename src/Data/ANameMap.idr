-- like name map, but able to return ambiguous names
module Data.ANameMap

import Core.Name
import Data.NameMap
import Data.StringMap

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
                          Just ns => filter (matches n) ns
	where
		-- Name matches if a prefix of the namespace matches a prefix of the
    -- namespace in the context
    matches : Name -> (Name, a) -> Bool
    matches (NS ns _) (NS cns _, _) = ns `isPrefixOf` cns
    matches (NS _ _) _ = True -- no in library name, so root doesn't match
    matches _ _ = True -- no prefix, so root must match, so good

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

-- Merge two contexts, with entries in the second overriding entries in
-- the first
export
merge : ANameMap a -> ANameMap a -> ANameMap a
merge ctxt (MkANameMap exact hier)
    = insertFrom (toList exact) ctxt
  where
    insertFrom : List (Name, a) -> ANameMap a -> ANameMap a
    insertFrom [] ctxt = ctxt
    insertFrom ((n, val) :: cs) ctxt
        = insertFrom cs (addName n val ctxt)

-- TODO: Update namespaces so 'as' works
export
mergeAs : List String -> List String ->
          ANameMap a -> ANameMap a -> ANameMap a
mergeAs oldns newns ctxt (MkANameMap exact hier)
    = insertFrom (toList exact) ctxt
  where
    insertFrom : List (Name, a) -> ANameMap a -> ANameMap a
    insertFrom [] ctxt = ctxt
    insertFrom ((n, val) :: cs) ctxt
        = insertFrom cs (addName n val ctxt)


