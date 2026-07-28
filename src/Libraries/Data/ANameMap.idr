-- like name map, but able to return ambiguous names
module Libraries.Data.ANameMap

import Core.Name

import Libraries.Data.NameMap
import Libraries.Data.UserNameMap

%default total

export
record ANameMap a where
     constructor MkANameMap
     -- for looking up by exact (completely qualified) names
     exactNames : NameMap a
     -- for looking up by name root or partially qualified (so possibly
     -- ambiguous) names. This doesn't store machine generated names.
     hierarchy : UserNameMap (List (Name, a))

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
            UserNameMap (List (Name, a)) -> UserNameMap (List (Name, a))
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

||| Remove a fully qualified name
export
removeExact : Show a => Name -> ANameMap a -> ANameMap a
removeExact n (MkANameMap dict hier)
    = let dict' = delete n dict
          n' = userNameRoot n
          hier' = maybe hier
                     (\foundName => deleteFromList foundName hier) n'
      in MkANameMap dict' hier'
  where
    -- When we find the list of namespace candidates, we need to remove the one that we are pointing
    -- at and leave the others untouched. We do this by filtering the list of candidates and removing
    -- the one that matches the namespace of the given name `n`. While we're using `filter`, there should
    -- only be one of them.
    deleteFromList : (un : UserName) -> (um : UserNameMap (List (Name, a))) -> UserNameMap (List (Name, a))
    deleteFromList un = adjust un (filter (\(key, _) => not $ key `matches` n))

export
toList : ANameMap a -> List (Name, a)
toList dict = toList (exactNames dict)

||| Export the list of name which are ambiguous without their namespace
export
toAmbiguousList : ANameMap a -> List (UserName, List a)
toAmbiguousList dict = map (mapSnd (map snd)) (toList dict.hierarchy)

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
