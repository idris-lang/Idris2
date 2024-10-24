import Data.SortedMap
import Data.List

%hide Data.SortedMap.toList -- deprecated and to be removed

toList : SortedMap k v -> List (k, v)
toList = kvList

f : Ord k => SortedMap k v -> List (k, v)
f m = case sortBy (\(x, _), (y, _) => compare x y) (Main.toList m) of
    as => as

g : Ord k => SortedMap k v -> List (k, v)
g m = let kvs = toList m in
          case sortBy (\(x, _), (y, _) => compare x y) kvs of
               as => as
