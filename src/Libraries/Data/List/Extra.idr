module Libraries.Data.List.Extra

import public Data.List
import Data.List1

%default total

export
minimum : Ord a => (xs : List a) -> {auto 0 _ : NonEmpty xs} -> a
minimum (x :: xs) = foldl min x xs

||| Fetches the element at a given position.
||| Returns `Nothing` if the position beyond the list's end.
public export
elemAt : List a -> Nat -> Maybe a
elemAt []        _     = Nothing
elemAt (l :: _)  Z     = Just l
elemAt (_ :: ls) (S n) = elemAt ls n

export
findBy : (a -> Maybe b) -> List a -> Maybe b
findBy p [] = Nothing
findBy p (x :: xs)
  = case p x of
      Nothing => findBy p xs
      Just win => pure win

export
breakAfter : (a -> Bool) -> List a -> (List a, List a)
breakAfter p [] = ([], [])
breakAfter p (x::xs)
    = if p x
         then ([x], xs)
         else let (ys, zs) = breakAfter p xs in (x::ys, zs)

export
splitAfter : (a -> Bool) -> List a -> List1 (List a)
splitAfter p xs
    = case breakAfter p xs of
           (chunk, []) => singleton chunk
           (chunk, rest@(_::_)) => cons chunk (splitAfter p (assert_smaller xs rest))

export
zipMaybe : List a -> List b -> Maybe (List (a, b))
zipMaybe [] [] = pure []
zipMaybe (a::as) (b::bs) = ((a, b) ::) <$> zipMaybe as bs
zipMaybe _ _ = Nothing

export
findBy' : (a -> Bool) -> List a -> (List a, Maybe a, List a)
findBy' f [] = ([], Nothing, [])
findBy' f (x :: xs) =
  case f x of
    True  => ([], Just x, xs)
    False =>
      let (pre, mb, post) = findBy' f xs in
      (x :: pre, mb, post)

||| Compute the difference of two lists by the given predicate.
||| Lists are treated as bags.
export
diffBy : (a -> a -> Bool)
      -> List a
      -> List a
      -> List a
diffBy f [] ys = []
diffBy f (x :: xs) ys =
  let whole@(pre, mb, post) = findBy' (f x) ys
      ys' = pre ++ post in
  case mb of
    Just _  =>      diffBy f xs ys'
    Nothing => x :: diffBy f xs ys'

||| Remove adjacent duplicates
export
dedup : Eq a => List a -> List a
dedup (a :: xs@(b :: _)) = if a == b then dedup xs else a :: dedup xs
dedup xs                = xs

||| O(n * log(n)). Sort a list and remove duplicates
export
sortedNub : Ord a => List a -> List a
sortedNub = dedup . sort

||| TODO: use the version in `Data.List1` in base after the next release.
export
groupBy : (a -> a -> Bool) -> List a -> List (List1 a)
groupBy _ [] = []
groupBy eq (h :: t) = let (ys,zs) = go h t
                       in ys :: zs

  where go : a -> List a -> (List1 a, List (List1 a))
        go v [] = (singleton v,[])
        go v (x :: xs) = let (ys,zs) = go x xs
                          in if eq v x
                                then (cons v ys, zs)
                                else (singleton v, ys :: zs)

||| TODO: use the version in `Data.List1` in base after the next release.
export
group : Eq a => List a -> List (List1 a)
group = Libraries.Data.List.Extra.groupBy (==)

||| TODO: use the version in `Data.List1` in base after the next release.
export
groupWith : Eq b => (a -> b) -> List a -> List (List1 a)
groupWith f = Libraries.Data.List.Extra.groupBy (\x,y => f x == f y)

||| TODO: use the version in `Data.List1` in base after the next release.
export
groupAllWith : Ord b => (a -> b) -> List a -> List (List1 a)
groupAllWith f = Libraries.Data.List.Extra.groupWith f . sortBy (comparing f)


||| TODO: use the version in `Data.List` in base after the next release.
public export
prefixOfBy : (match : a -> b -> Maybe m) ->
             (left : List a) -> (right : List b) ->
             Maybe (List m, List b)
prefixOfBy p = go [<] where
  chips : forall a. SnocList a -> List a -> List a
  chips [<] xs = xs
  chips (xz :< x) xs = chips xz (x :: xs)
  go : SnocList m -> List a -> List b -> Maybe (List m, List b)
  go sm [] bs = pure (chips sm [], bs)
  go sm as [] = Nothing
  go sm (a :: as) (b :: bs) = go (sm :< !(p a b)) as bs

||| TODO: use the version in `Data.List` in base after the next release.
public export
suffixOfBy : (match : a -> b -> Maybe m) ->
             (left : List a) -> (right : List b) ->
             Maybe (List b, List m)
suffixOfBy match left right
  = do (ms, bs) <- Extra.prefixOfBy match (reverse left) (reverse right)
       pure (reverse bs, reverse ms)
