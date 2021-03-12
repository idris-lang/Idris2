module Libraries.Data.StringTrie

import Data.These
import Libraries.Data.StringMap

%default total

-- prefix tree specialised to use `String`s as keys

public export
record StringTrie a where
  constructor MkStringTrie
  node : These a (StringMap (StringTrie a))

public export
Show a => Show (StringTrie a) where
  show (MkStringTrie node) = assert_total $ show node

public export
Functor StringTrie where
  map f (MkStringTrie node) = MkStringTrie $ assert_total $ bimap f (map (map f)) node

public export
empty : StringTrie a
empty = MkStringTrie $ That empty

public export
singleton : List String -> a -> StringTrie a
singleton []      v = MkStringTrie $ This v
singleton (k::ks) v = MkStringTrie $ That $ singleton k (singleton ks v)

-- insert using supplied function to resolve clashes
public export
insertWith : List String -> (Maybe a -> a) -> StringTrie a -> StringTrie a
insertWith []      f (MkStringTrie nd) =
  MkStringTrie $ these (This . f . Just) (Both (f Nothing)) (Both . f . Just) nd
insertWith (k::ks) f (MkStringTrie nd) =
  MkStringTrie $ these (\x => Both x (singleton k end)) (That . rec) (\x => Both x . rec) nd
  where
  end : StringTrie a
  end = singleton ks (f Nothing)
  rec : StringMap (StringTrie a) -> StringMap (StringTrie a)
  rec sm = maybe (insert k end sm) (\tm => insert k (insertWith ks f tm) sm) (lookup k sm)

public export
insert : List String -> a -> StringTrie a -> StringTrie a
insert ks v = insertWith ks (const v)

-- fold the trie in a depth-first fashion performing monadic actions on values, then keys
-- note that for `Both` the action on node values will be performed first because of `bitraverse` implementation
public export
foldWithKeysM : (Monad m, Monoid b) => (List String -> m b) -> (List String -> a -> m b) -> StringTrie a -> m b
foldWithKeysM {a} {m} {b} fk fv = go []
  where
  go : List String -> StringTrie a -> m b
  go ks (MkStringTrie nd) =
    bifold <$> bitraverse
                (fv ks)
                (\sm => foldlM
                          (\x, (k, vs) => do let ks' = ks++[k]
                                             y <- assert_total $ go ks' vs
                                             z <- fk ks'
                                             pure $ x <+> y <+> z)
                          neutral
                          (toList sm))
                nd

-- search the trie for a specific path of strings
public export
find : List String -> StringTrie a -> Maybe a 
-- If our "path" has finished, and this node in the trie has some "data", return it.
find [] (MkStringTrie (This x)) = Just x
find [] (MkStringTrie (Both x _)) = Just x
-- If we still have some path left, search the children for the head of the path.
find (y :: ys) (MkStringTrie (That children)) = (lookup y children) >>= (find ys)
find (y :: ys) (MkStringTrie (Both _ children)) = (lookup y children) >>= (find ys)
-- Otherwise, we can't find what we're looking for (path too short, or too long)
find _ _ = Nothing