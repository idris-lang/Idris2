module Libraries.Data.List.Extra

import Data.List
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
