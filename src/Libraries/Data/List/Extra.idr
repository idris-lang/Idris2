module Libraries.Data.List.Extra

import public Data.List

%default total

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

export
lengthDistributesOverAppend
  : (xs, ys : List a)
  -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys =
  cong S $ lengthDistributesOverAppend xs ys
