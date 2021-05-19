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
                          (StringMap.toList sm))
                nd
