module Data.List

import public Control.Function

import Data.Nat
import Data.List1
import Data.Fin
import public Data.Zippable

%default total

||| Boolean check for whether the list is the empty list.
public export
isNil : List a -> Bool
isNil [] = True
isNil _  = False

||| Boolean check for whether the list contains a cons (::) / is non-empty.
public export
isCons : List a -> Bool
isCons [] = False
isCons _  = True

||| Add an element to the end of a list.
||| O(n). See the `Data.SnocList` module if you need to perform `snoc` often.
public export
snoc : List a -> a -> List a
snoc xs x = xs ++ [x]

||| Take `n` first elements from `xs`, returning the whole list if
||| `n` >= length `xs`.
|||
||| @ n  the number of elements to take
||| @ xs the list to take the elements from
public export
take : (n : Nat) -> (xs : List a) -> List a
take (S k) (x :: xs) = x :: take k xs
take _ _ = []

||| Remove `n` first elements from `xs`, returning the empty list if
||| `n >= length xs`
|||
||| @ n  the number of elements to remove
||| @ xs the list to drop the elements from
public export
drop : (n : Nat) -> (xs : List a) -> List a
drop Z     xs      = xs
drop (S n) []      = []
drop (S n) (_::xs) = drop n xs

||| Satisfiable if `k` is a valid index into `xs`.
|||
||| @ k  the potential index
||| @ xs the list into which k may be an index
public export
data InBounds : (k : Nat) -> (xs : List a) -> Type where
    ||| Z is a valid index into any cons cell
    InFirst : InBounds Z (x :: xs)
    ||| Valid indices can be extended
    InLater : InBounds k xs -> InBounds (S k) (x :: xs)

public export
Uninhabited (InBounds k []) where
  uninhabited InFirst impossible
  uninhabited (InLater _) impossible

export
Uninhabited (InBounds k xs) => Uninhabited (InBounds (S k) (x::xs)) where
  uninhabited (InLater y) = uninhabited y

||| Decide whether `k` is a valid index into `xs`.
public export
inBounds : (k : Nat) -> (xs : List a) -> Dec (InBounds k xs)
inBounds _ [] = No uninhabited
inBounds Z (_ :: _) = Yes InFirst
inBounds (S k) (x :: xs) with (inBounds k xs)
  inBounds (S k) (x :: xs) | (Yes prf) = Yes (InLater prf)
  inBounds (S k) (x :: xs) | (No contra)
      = No $ \(InLater y) => contra y

||| Find a particular element of a list.
|||
||| @ ok a proof that the index is within bounds
public export
index : (n : Nat) -> (xs : List a) -> {auto 0 ok : InBounds n xs} -> a
index Z (x :: xs) {ok = InFirst} = x
index (S k) (_ :: xs) {ok = InLater _} = index k xs

public export
index' : (xs : List a) -> Fin (length xs) -> a
index' (x::_)  FZ     = x
index' (_::xs) (FS i) = index' xs i

||| Generate a list by repeatedly applying a partial function until exhausted.
||| @ f the function to iterate
||| @ x the initial value that will be the head of the list
covering
public export
iterate : (f : a -> Maybe a) -> (x : a) -> List a
iterate f x  = x :: case f x of
  Nothing => []
  Just y => iterate f y

||| Given a function `f` which extracts an element of `b` and `b`'s
||| continuation, return the list consisting of the extracted elements.
||| CAUTION: Only terminates if `f` eventually returns `Nothing`.
|||
||| @ f  a function which provides an element of `b` and the rest of `b`
||| @ b  a structure contanining any number of elements
covering
public export
unfoldr : (f : b -> Maybe (a, b)) -> b -> List a
unfoldr f c = case f c of
  Nothing     => []
  Just (a, n) => a :: unfoldr f n

||| Returns the list of elements obtained by applying `f` to `x` `0` to `n-1` times,
||| starting with `x`.
|||
||| @ n  the number of times to iterate `f` over `x`
||| @ f  a function producing a series
||| @ x  the initial element of the series
public export
iterateN : (n : Nat) -> (f : a -> a) -> (x : a) -> List a
iterateN Z     _ _ = []
iterateN (S k) f x = x :: iterateN k f (f x)

||| Get the longest prefix of the list that satisfies the predicate.
|||
||| @ p  a custom predicate for the elements of the list
||| @ xs the list of elements
public export
takeWhile : (p : a -> Bool) -> (xs : List a) -> List a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

||| Remove elements from the list until an element no longer satisfies the
||| predicate.
|||
||| @ p  a custom predicate for the elements of the list
||| @ xs the list of elements to remove from
public export
dropWhile : (p : a -> Bool) -> (xs : List a) -> List a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

||| Find the first element of the list that satisfies the predicate.
public export
find : (p : a -> Bool) -> (xs : List a) -> Maybe a
find p [] = Nothing
find p (x::xs) = if p x then Just x else find p xs

||| Find the index and proof of InBounds of the first element (if exists) of a
||| list that satisfies the given test, else `Nothing`.
public export
findIndex : (a -> Bool) -> (xs : List a) -> Maybe $ Fin (length xs)
findIndex _ [] = Nothing
findIndex p (x :: xs) = if p x
  then Just FZ
  else FS <$> findIndex p xs

||| Find indices of all elements that satisfy the given test.
public export
findIndices : (a -> Bool) -> List a -> List Nat
findIndices p = h 0 where
  h : Nat -> List a -> List Nat
  h _         []  = []
  h lvl (x :: xs) = if p x
    then lvl :: h (S lvl) xs
    else        h (S lvl) xs

||| Find associated information in a list using a custom comparison.
public export
lookupBy : (a -> b -> Bool) -> a -> List (b, v) -> Maybe v
lookupBy p e []      = Nothing
lookupBy p e ((l, r) :: xs) =
  if p e l then
    Just r
  else
    lookupBy p e xs

||| Find associated information in a list using Boolean equality.
public export
lookup : Eq a => a -> List (a, b) -> Maybe b
lookup = lookupBy (==)

||| Remove duplicate elements from a list using a custom comparison. The general
||| case of `nub`.
||| O(n^2).
|||
||| @ p  a custom comparison for detecting duplicate elements
||| @ xs the list to remove the duplicates from
public export
nubBy : (p : a -> a -> Bool) -> (xs : List a) -> List a
nubBy = nubBy' []
  where
    nubBy' : List a -> (a -> a -> Bool) -> List a -> List a
    nubBy' acc p []      = []
    nubBy' acc p (x::xs) =
      if elemBy p x acc then
        nubBy' acc p xs
      else
        x :: nubBy' (x::acc) p xs

||| The nub function removes duplicate elements from a list using
||| boolean equality. In particular, it keeps only the first occurrence of each
||| element. It is a special case of `nubBy`, which allows the programmer to
||| supply their own equality test.
||| O(n^2).
|||
||| ```idris example
||| nub (the (List _) [1,2,1,3])
||| ```
public export
nub : Eq a => List a -> List a
nub = nubBy (==)

||| Insert an element at a particular index.
|||
||| ```idris example
||| insertAt 1 [6, 8, 9] 7
||| ```
|||
||| @idx The index of the inserted value in the resulting list.
||| @x The value to insert.
||| @xs The list to insert the value into.
public export
insertAt : (idx : Nat) -> (x : a) -> (xs : List a) -> {auto 0 ok : idx `LTE` length xs} -> List a
insertAt Z x xs = x :: xs
insertAt {ok=LTESucc _} (S n) x (y :: ys) = y :: (insertAt n x ys)

||| Construct a new list consisting of all but the indicated element.
|||
||| ```idris example
||| deleteAt 3 [5, 6, 7, 8, 9]
||| ```
|||
||| @ idx The index of the value to delete.
||| @ xs The list to delete the value from.
public export
deleteAt : (idx : Nat) -> (xs : List a) -> {auto 0 prf : InBounds idx xs} -> List a
deleteAt {prf=InFirst} Z (_ :: xs) = xs
deleteAt {prf=InLater _} (S k) (x :: xs) = x :: deleteAt k xs

||| The deleteBy function behaves like delete, but takes a user-supplied equality predicate.
public export
deleteBy : (a -> b -> Bool) -> a -> List b -> List b
deleteBy _  _ []      = []
deleteBy eq x (y::ys) = if x `eq` y then ys else y :: deleteBy eq x ys

||| `delete x` removes the first occurrence of `x` from its list argument. For
||| example,
|||
|||````idris example
|||delete 'a' ['b', 'a', 'n', 'a', 'n', 'a']
|||````
|||
||| It is a special case of deleteBy, which allows the programmer to supply
||| their own equality test.
public export
delete : Eq a => a -> List a -> List a
delete = deleteBy (==)

||| Delete the first occurrence of each element from the second list in the first
||| list where equality is determined by the predicate passed as the first argument.
||| @ p            A function that returns true when its two arguments should be considered equal.
||| @ source       The list to delete elements from.
||| @ undesirables The list of elements to delete.
public export
deleteFirstsBy : (p : a -> b -> Bool) -> (source : List b) -> (undesirables : List a) -> List b
deleteFirstsBy p = foldl (flip (deleteBy p))

infix 7 \\

||| The non-associative list-difference.
||| A specialized form of @deleteFirstsBy@ where the predicate is equality under the @Eq@
||| interface.
||| Deletes the first occurrence of each element of the second list from the first list.
|||
||| In the following example, the result is `[2, 4]`.
||| ```idris example
||| [1, 2, 3, 4] // [1, 3]
||| ```
|||
public export
(\\) : Eq a => List a -> List a -> List a
(\\) = foldl (flip delete)

||| The unionBy function returns the union of two lists by user-supplied equality predicate.
public export
unionBy : (a -> a -> Bool) -> List a -> List a -> List a
unionBy eq xs ys = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

||| Compute the union of two lists according to their `Eq` implementation.
|||
||| ```idris example
||| union ['d', 'o', 'g'] ['c', 'o', 'w']
||| ```
|||
public export
union : Eq a => List a -> List a -> List a
union = unionBy (==)

||| Like @span@ but using a predicate that might convert a to b, i.e. given a
||| predicate from a to Maybe b and a list of as, returns a tuple consisting of
||| the longest prefix of the list where a -> Just b, and the rest of the list.
public export
spanBy : (a -> Maybe b) -> List a -> (List b, List a)
spanBy p [] = ([], [])
spanBy p (x :: xs) = case p x of
  Nothing => ([], x :: xs)
  Just y => let (ys, zs) = spanBy p xs in (y :: ys, zs)

||| Given a predicate and a list, returns a tuple consisting of the longest
||| prefix of the list whose elements satisfy the predicate, and the rest of the
||| list.
public export
span : (a -> Bool) -> List a -> (List a, List a)
span p []      = ([], [])
span p (x::xs) =
  if p x then
    let (ys, zs) = span p xs in
        (x::ys, zs)
  else
    ([], x::xs)

||| Similar to `span` but negates the predicate, i.e.: returns a tuple
||| consisting of the longest prefix of the list whose elements don't satisfy
||| the predicate, and the rest of the list.
public export
break : (a -> Bool) -> List a -> (List a, List a)
break p xs = span (not . p) xs

public export
singleton : a -> List a
singleton x = [x]

public export
split : (a -> Bool) -> List a -> List1 (List a)
split p xs =
  case break p xs of
    (chunk, [])          => singleton chunk
    (chunk, (c :: rest)) => chunk ::: forget (split p (assert_smaller xs rest))

||| Split the list `xs` at the index `n`. If `n > length xs`, returns a tuple
||| consisting of `xs` and `[]`.
|||
||| @ n  the index to split the list at
||| @ xs the list to split
public export
splitAt : (n : Nat) -> (xs : List a) -> (List a, List a)
splitAt Z xs = ([], xs)
splitAt (S k) [] = ([], [])
splitAt (S k) (x :: xs)
      = let (tk, dr) = splitAt k xs in
            (x :: tk, dr)

||| Divide the list into a tuple containing two smaller lists: one with the
||| elements that satisfies the given predicate and another with the elements
||| that don't.
|||
||| @ p  the predicate to partition according to
||| @ xs the list to partition
public export
partition : (p : a -> Bool) -> (xs : List a) -> (List a, List a)
partition p []      = ([], [])
partition p (x::xs) =
  let (lefts, rights) = partition p xs in
    if p x then
      (x::lefts, rights)
    else
      (lefts, x::rights)

||| The inits function returns all initial segments of the argument, shortest
||| first. For example,
|||
||| ```idris example
||| inits [1,2,3]
||| ```
public export
inits : List a -> List (List a)
inits xs = [] :: case xs of
  []        => []
  x :: xs'  => map (x ::) (inits xs')

||| The tails function returns all final segments of the argument, longest
||| first. For example,
|||
||| ```idris example
||| tails [1,2,3] == [[1,2,3], [2,3], [3], []]
|||```
public export
tails : List a -> List (List a)
tails xs = xs :: case xs of
  []        => []
  _ :: xs'  => tails xs'

||| Split on the given element.
|||
||| ```idris example
||| splitOn 0 [1,0,2,0,0,3]
||| ```
|||
public export
splitOn : Eq a => a -> List a -> List1 (List a)
splitOn a = split (== a)

||| Replace an element at a particlar index with another.
|||
||| ```idris example
||| replaceAt 2 6 [1, 2, 3, 4]
||| ```
|||
||| @idx The index of the value to replace.
||| @x The value to insert.
||| @xs The list in which to replace an element.
public export
replaceAt : (idx : Nat) -> a -> (xs : List a) -> {auto 0 ok : InBounds idx xs} -> List a
replaceAt Z y (_ :: xs) {ok=InFirst} = y :: xs
replaceAt (S k) y (x :: xs) {ok=InLater _} = x :: replaceAt k y xs

||| Replace the elements in the list that satisfy the predicate with the given
||| value. The general case of `replaceOn`.
|||
||| @ p  the predicate to replace elements in the list according to
||| @ b  the element to replace with
||| @ l  the list to perform the replacements on
public export
replaceWhen : (p : a -> Bool) -> (b : a) -> (l : List a) -> List a
replaceWhen p b l = map (\c => if p c then b else c) l

||| Replace the elements in the list that are equal to `e`, using boolean
||| equality, with `b`. A special case of `replaceWhen`, using `== e` as the
||| predicate.
|||
||| ```idris example
||| > replaceOn '-' ',' ['1', '-', '2', '-', '3']
||| ['1', ',', '2', ',', '3']
||| ```
|||
||| @ e  the element to find and replace
||| @ b  the element to replace with
||| @ l  the list to perform the replacements on
public export
replaceOn : Eq a => (e : a) -> (b : a) -> (l : List a) -> List a
replaceOn e = replaceWhen (== e)

replicateTR : List a -> Nat -> a -> List a
replicateTR as Z     _ = as
replicateTR as (S n) x = replicateTR (x :: as) n x

||| Construct a list with `n` copies of `x`.
|||
||| @ n how many copies
||| @ x the element to replicate
public export
replicate : (n : Nat) -> (x : a) -> List a
replicate Z     _ = []
replicate (S n) x = x :: replicate n x

-- Data.List.replicateTRIsReplicate proves these are equivalent.
%transform "tailRecReplicate" List.replicate = List.replicateTR Nil


||| Compute the intersect of two lists by user-supplied equality predicate.
export
intersectBy : (a -> a -> Bool) -> List a -> List a -> List a
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

||| Compute the intersection of two lists according to the `Eq` implementation for
||| the elements.
export
intersect : Eq a => List a -> List a -> List a
intersect = intersectBy (==)

||| Compute the intersect of all the lists in the given list of lists, according
||| to the user-supplied equality predicate.
|||
||| @ eq the predicate for computing the intersection
||| @ ls the list of lists to compute the intersect of
export
intersectAllBy : (eq : a -> a -> Bool) -> (ls : List (List a)) -> List a
intersectAllBy eq [] = []
intersectAllBy eq (xs :: xss) = filter (\x => all (elemBy eq x) xss) xs

||| Compute the intersect of all the lists in the given list of lists, according
||| to boolean equality. A special case of `intersectAllBy`, using `==` as the
||| equality predicate.
|||
||| @ ls the list of lists to compute the intersect of
export
intersectAll : Eq a => (ls : List (List a)) -> List a
intersectAll = intersectAllBy (==)

---------------------------
-- Zippable --
---------------------------

public export
Zippable List where
  zipWith _ [] _ = []
  zipWith _ _ [] = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  zipWith3 _ [] _ _ = []
  zipWith3 _ _ [] _ = []
  zipWith3 _ _ _ [] = []
  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

  unzipWith f [] = ([], [])
  unzipWith f (x :: xs) = let (b, c) = f x
                              (bs, cs) = unzipWith f xs in
                              (b :: bs, c :: cs)

  unzipWith3 f [] = ([], [], [])
  unzipWith3 f (x :: xs) = let (b, c, d) = f x
                               (bs, cs, ds) = unzipWith3 f xs in
                               (b :: bs, c :: cs, d :: ds)

---------------------------
-- Non-empty List
---------------------------

||| Proof that a given list is non-empty.
public export
data NonEmpty : (xs : List a) -> Type where
    IsNonEmpty : NonEmpty (x :: xs)

-- The empty list (Nil) cannot be `NonEmpty`.
export
Uninhabited (NonEmpty []) where
  uninhabited IsNonEmpty impossible

||| Get the head of a non-empty list.
||| @ ok proof the list is non-empty
public export
head : (l : List a) -> {auto 0 ok : NonEmpty l} -> a
head [] impossible
head (x :: _) = x

||| Get the tail of a non-empty list.
||| @ ok proof the list is non-empty
public export
tail : (l : List a) -> {auto 0 ok : NonEmpty l} -> List a
tail [] impossible
tail (_ :: xs) = xs

||| Retrieve the last element of a non-empty list.
||| @ ok proof that the list is non-empty
public export
last : (l : List a) -> {auto 0 ok : NonEmpty l} -> a
last [] impossible
last [x] = x
last (x :: xs@(_::_)) = last xs

||| Return all but the last element of a non-empty list.
||| @ ok proof the list is non-empty
public export
init : (l : List a) -> {auto 0 ok : NonEmpty l} -> List a
init [] impossible
init [x] = []
init (x :: xs@(_::_)) = x :: init xs

||| Attempt to get the head of a list. If the list is empty, return `Nothing`.
public export
head' : List a -> Maybe a
head' []      = Nothing
head' (x::_) = Just x

||| Attempt to get the tail of a list. If the list is empty, return `Nothing`.
export
tail' : List a -> Maybe (List a)
tail' []      = Nothing
tail' (_::xs) = Just xs

||| Attempt to retrieve the last element of a non-empty list.
|||
||| If the list is empty, return `Nothing`.
export
last' : List a -> Maybe a
last' [] = Nothing
last' xs@(_::_) = Just (last xs)

||| Attempt to return all but the last element of a non-empty list.
|||
||| If the list is empty, return `Nothing`.
export
init' : List a -> Maybe (List a)
init' [] = Nothing
init' xs@(_::_) = Just (init xs)

||| Foldr a non-empty list, using `map` to transform the first accumulated
||| element to something of the desired type and `func` to accumulate the
||| elements.
|||
||| @ func the function used to accumulate the elements
||| @ map  an initial transformation from the element to the accumulated type
||| @ l    the non-empty list to foldr
||| @ ok   proof that the list is non-empty
public export
foldr1By : (func : a -> b -> b) -> (map : a -> b) ->
           (l : List a) -> {auto 0 ok : NonEmpty l} -> b
foldr1By f map [] impossible
foldr1By f map [x] = map x
foldr1By f map (x :: xs@(_::_)) = f x (foldr1By f map xs)

||| Foldl a non-empty list, using `map` to transform the first accumulated
||| element to something of the desired type and `func` to accumulate the
||| elements.
|||
||| @ func the function used to accumulate the elements
||| @ map  an initial transformation from the element to the accumulated type
||| @ l    the non-empty list to foldl
||| @ ok   proof that the list is non-empty
public export
foldl1By : (func : b -> a -> b) -> (map : a -> b) ->
           (l : List a) -> {auto 0 ok : NonEmpty l} -> b
foldl1By f map [] impossible
foldl1By f map (x::xs) = foldl f (map x) xs

||| Foldr a non-empty list without seeding the accumulator.
|||
||| @ ok proof that the list is non-empty
public export
foldr1 : (a -> a -> a) -> (l : List a) -> {auto 0 ok : NonEmpty l} -> a
foldr1 f xs = foldr1By f id xs

||| Foldl a non-empty list without seeding the accumulator.
|||
||| @ ok proof that the list is non-empty
public export
foldl1 : (a -> a -> a) -> (l : List a) -> {auto 0 ok : NonEmpty l} -> a
foldl1 f xs = foldl1By f id xs

||| Convert to a non-empty list.
|||
||| @ ok proof the list is non-empty
export
toList1 : (l : List a) -> {auto 0 ok : NonEmpty l} -> List1 a
toList1 [] impossible
toList1 (x :: xs) = x ::: xs

||| Convert to a non-empty list, returning Nothing if the list is empty.
public export
toList1' : (l : List a) -> Maybe (List1 a)
toList1' [] = Nothing
toList1' (x :: xs) = Just (x ::: xs)

||| Interleave two lists.
||| ```idris example
||| > interleave ["a", "c", "e"]  ["b", "d", "f"]
||| ["a", "b", "c", "d", "e", "f"]
||| ```
public export
interleave : (xs, ys : List a) -> List a
interleave [] ys = ys
interleave (x :: xs) ys = x :: interleave ys xs

||| Prefix every element in the list with the given element.
|||
||| @ sep the value to prefix
||| @ xs  the list of elements to prefix with the given element
|||
||| ```idris example
||| > with List (mergeReplicate '>' ['a', 'b', 'c', 'd', 'e'])
||| ['>', 'a', '>', 'b', '>', 'c', '>', 'd', '>', 'e']
||| ```
public export
mergeReplicate : (sep : a) -> (xs : List a) -> List a
mergeReplicate sep []      = []
mergeReplicate sep (y::ys) = sep :: y :: mergeReplicate sep ys

||| Insert some separator between the elements of a list.
|||
||| @ sep the value to intersperse
||| @ xs  the list of elements to intersperse with the separator
|||
||| ```idris example
||| > with List (intersperse ',' ['a', 'b', 'c', 'd', 'e'])
||| ['a', ',', 'b', ',', 'c', ',', 'd', ',', 'e']
||| ```
public export
intersperse : (sep : a) -> (xs : List a) -> List a
intersperse sep []      = []
intersperse sep (x::xs) = x :: mergeReplicate sep xs

||| Given a separator list and some more lists, produce a new list by
||| placing the separator between each of the lists.
|||
||| @ sep the separator
||| @ xss the lists between which the separator will be placed
|||
||| ```idris example
||| intercalate [0, 0, 0] [ [1, 2, 3], [4, 5, 6], [7, 8, 9] ]
||| ```
export
intercalate : (sep : List a) -> (xss : List (List a)) -> List a
intercalate sep xss = concat $ intersperse sep xss

||| Extract all of the values contained in a List of Maybes
public export
catMaybes : List (Maybe a) -> List a
catMaybes = mapMaybe id

--------------------------------------------------------------------------------
-- Sorting
--------------------------------------------------------------------------------

||| Check whether a list is sorted with respect to the default ordering for the type of its elements.
export
sorted : Ord a => List a -> Bool
sorted (x :: xs @ (y :: _)) = x <= y && sorted xs
sorted _ = True

||| Merge two sorted lists using an arbitrary comparison
||| predicate. Note that the lists must have been sorted using this
||| predicate already.
export
mergeBy : (a -> a -> Ordering) -> List a -> List a -> List a
mergeBy order []      right   = right
mergeBy order left    []      = left
mergeBy order (x::xs) (y::ys) =
  -- The code below will emit `y` before `x` whenever `x == y`.
  -- If you change this, `sortBy` will stop being stable, unless you fix `sortBy`, too.
  case order x y of
       LT => x :: mergeBy order xs (y::ys)
       _  => y :: mergeBy order (x::xs) ys

||| Merge two sorted lists using the default ordering for the type of their elements.
export
merge : Ord a => List a -> List a -> List a
merge left right = mergeBy compare left right

||| Sort a list using some arbitrary comparison predicate.
|||
||| @ cmp how to compare elements
||| @ xs the list to sort
export
sortBy : (cmp : a -> a -> Ordering) -> (xs : List a) -> List a
sortBy cmp []  = []
sortBy cmp [x] = [x]
sortBy cmp xs  = let (x, y) = split xs in
    mergeBy cmp
          (sortBy cmp (assert_smaller xs x))
          (sortBy cmp (assert_smaller xs y)) -- not structurally smaller, hence assert
  where
    splitRec : List b -> List a -> (List a -> List a) -> (List a, List a)
    splitRec (_::_::xs) (y::ys) zs = splitRec xs ys (zs . ((::) y))
    splitRec _          ys      zs = (ys, zs [])
    -- In the above base-case clause, we put `ys` on the LHS to get a stable sort.
    -- This is because `mergeBy` prefers taking elements from its RHS operand
    -- if both heads are equal, and all elements in `zs []` precede all elements of `ys`
    -- in the original list.

    split : List a -> (List a, List a)
    split xs = splitRec xs xs id

||| Sort a list using the default ordering for the type of its elements.
export
sort : Ord a => List a -> List a
sort = sortBy compare

||| Check whether the `left` list is a prefix of the `right` one, according to
||| `match`. Returns the matched prefix together with the leftover suffix.
|||
||| @ match a custom matching function for checking the elements are convertible
||| @ left  the list which might be a prefix of `right`
||| @ right the list of elements to compare against
public export
prefixOfBy : (match : a -> b -> Maybe m) ->
             (left : List a) -> (right : List b) ->
             Maybe (List m, List b)
prefixOfBy p = go [<] where
  go : SnocList m -> List a -> List b -> Maybe (List m, List b)
  go sm [] bs = pure (sm <>> [], bs)
  go sm as [] = Nothing
  go sm (a :: as) (b :: bs) = go (sm :< !(p a b)) as bs

||| Check whether the `left` list is a prefix of the `right` one, using the
||| provided equality function to compare elements.
|||
||| @ eq    a custom equality function for comparing the elements
||| @ left  the list which might be a prefix of `right`
||| @ right the list of elements to compare againts
public export
isPrefixOfBy : (eq : a -> b -> Bool) ->
               (left : List a) -> (right : List b) -> Bool
isPrefixOfBy p [] _            = True
isPrefixOfBy p _ []            = False
isPrefixOfBy p (x::xs) (y::ys) = p x y && isPrefixOfBy p xs ys

||| The isPrefixOf function takes two lists and returns True iff the first list
||| is a prefix of the second when comparing elements using `==`.
public export
isPrefixOf : Eq a => List a -> List a -> Bool
isPrefixOf = isPrefixOfBy (==)

||| Check whether the `left` is a suffix of the `right` one, according to
||| `match`. Returns the matched suffix together with the leftover prefix.
|||
||| @ match a custom matching function for checking the elements are convertible
||| @ left  the list which might be a prefix of `right`
||| @ right the list of elements to compare against
public export
suffixOfBy : (match : a -> b -> Maybe m) ->
             (left : List a) -> (right : List b) ->
             Maybe (List b, List m)
suffixOfBy match left right
  = do (ms, bs) <- prefixOfBy match (reverse left) (reverse right)
       pure (reverse bs, reverse ms)

||| Check whether the `left` is a suffix of the `right` one, using the provided
||| equality function to compare elements.
|||
||| @ eq    a custom equality function for comparing the elements
||| @ left  the list which might be a suffix of `right`
||| @ right the list of elements to compare againts
public export
isSuffixOfBy : (eq : a -> b -> Bool) ->
               (left : List a) -> (right : List b) -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

||| The isSuffixOf function takes two lists and returns True iff the first list
||| is a suffix of the second when comparing elements using `==`.
public export
isSuffixOf : Eq a => List a -> List a -> Bool
isSuffixOf = isSuffixOfBy (==)

||| The isInfixOf function takes two lists and returns True iff the first list
||| is contained, wholly and intact, anywhere within the second.
|||
||| ```idris example
||| isInfixOf ['b','c'] ['a', 'b', 'c', 'd']
||| ```
||| ```idris example
||| isInfixOf ['b','d'] ['a', 'b', 'c', 'd']
||| ```
|||
public export
isInfixOf : Eq a => List a -> List a -> Bool
isInfixOf n h = any (isPrefixOf n) (tails h)

||| Transposes rows and columns of a list of lists.
|||
||| ```idris example
||| with List transpose [[1, 2], [3, 4]]
||| ```
|||
||| This also works for non square scenarios, thus
||| involution does not always hold:
|||
|||     transpose [[], [1, 2]] = [[1], [2]]
|||     transpose (transpose [[], [1, 2]]) = [[1, 2]]
export
transpose : List (List a) -> List (List a)
transpose [] = []
transpose (heads :: tails) = spreadHeads heads (transpose tails) where
  spreadHeads : List a -> List (List a) -> List (List a)
  spreadHeads []              tails           = tails
  spreadHeads (head :: heads) []              = [head] :: spreadHeads heads []
  spreadHeads (head :: heads) (tail :: tails) = (head :: tail) :: spreadHeads heads tails

------------------------------------------------------------------------
-- Grouping
------------------------------------------------------------------------

||| `groupBy` operates like `group`, but uses the provided equality
||| predicate instead of `==`.
public export
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

||| The `group` function takes a list of values and returns a list of
||| lists such that flattening the resulting list is equal to the
||| argument.  Moreover, each list in the resulting list
||| contains only equal elements.
public export
group : Eq a => List a -> List (List1 a)
group = groupBy (==)

||| `groupWith` operates like `group`, but uses the provided projection when
||| comparing for equality
public export
groupWith : Eq b => (a -> b) -> List a -> List (List1 a)
groupWith f = groupBy (\x,y => f x == f y)

||| `groupAllWith` operates like `groupWith`, but sorts the list
||| first so that each equivalence class has, at most, one list in the
||| output
public export
groupAllWith : Ord b => (a -> b) -> List a -> List (List1 a)
groupAllWith f = groupWith f . sortBy (comparing f)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- Nil is not Cons
export
Uninhabited ([] = x :: xs) where
  uninhabited Refl impossible

-- Cons is not Nil
export
Uninhabited (x :: xs = []) where
  uninhabited Refl impossible

-- If the heads or the tails of two lists are provably non-equal, then the
-- combination of the respective heads with their respective tails must be
-- provably non-equal.
export
{0 xs : List a} -> Either (Uninhabited $ x === y) (Uninhabited $ xs === ys) => Uninhabited (x::xs = y::ys) where
  uninhabited @{Left  z} Refl = uninhabited @{z} Refl
  uninhabited @{Right z} Refl = uninhabited @{z} Refl

||| (::) is injective
export
Biinjective Prelude.(::) where
  biinjective Refl = (Refl, Refl)

||| Heterogeneous injectivity for (::)
export
consInjective : forall x, xs, y, ys .
                the (List a) (x :: xs) = the (List b) (y :: ys) -> (x = y, xs = ys)
consInjective Refl = (Refl, Refl)

lengthPlusIsLengthPlus : (n : Nat) -> (xs : List a) ->
                         lengthPlus n xs = n + length xs
lengthPlusIsLengthPlus n [] = sym $ plusZeroRightNeutral n
lengthPlusIsLengthPlus n (x::xs) =
  trans
  (lengthPlusIsLengthPlus (S n) xs)
  (plusSuccRightSucc n (length xs))

lengthTRIsLength : (xs : List a) -> lengthTR xs = length xs
lengthTRIsLength = lengthPlusIsLengthPlus Z

||| List `reverse` applied to `reverseOnto` is equivalent to swapping the
||| arguments of `reverseOnto`.
reverseReverseOnto : (l, r : List a) ->
                     reverse (reverseOnto l r) = reverseOnto r l
reverseReverseOnto _ [] = Refl
reverseReverseOnto l (x :: xs) = reverseReverseOnto (x :: l) xs

||| List `reverse` applied twice yields the identity function.
export
reverseInvolutive : (xs : List a) -> reverse (reverse xs) = xs
reverseInvolutive = reverseReverseOnto []

||| Appending `x` to `l` and then reversing the result onto `r` is the same as
||| using (::) with `x` and the result of reversing `l` onto `r`.
consReverse : (x : a) -> (l, r : List a) ->
              x :: reverseOnto r l = reverseOnto r (reverseOnto [x] (reverse l))
consReverse _ [] _ = Refl
consReverse x (y::ys) r
  = rewrite consReverse x ys (y :: r) in
      rewrite cong (reverseOnto r . reverse) $ consReverse x ys [y] in
        rewrite reverseInvolutive (y :: reverseOnto [x] (reverse ys)) in
          Refl

||| Proof that it is safe to lift a (::) out of the first `tailRecAppend`
||| argument.
consTailRecAppend : (x : a) -> (l, r : List a) ->
                    tailRecAppend (x :: l) r = x :: (tailRecAppend l r)
consTailRecAppend x l r
  = rewrite consReverse x (reverse l) r in
      rewrite reverseInvolutive l in
        Refl

||| Proof that `(++)` and `tailRecAppend` do the same thing, so the %transform
||| directive is safe.
tailRecAppendIsAppend : (xs, ys : List a) -> tailRecAppend xs ys = xs ++ ys
tailRecAppendIsAppend [] ys = Refl
tailRecAppendIsAppend (x::xs) ys =
  trans (consTailRecAppend x xs ys) (cong (x ::) $ tailRecAppendIsAppend xs ys)

||| The empty list is a right identity for append.
export
appendNilRightNeutral : (l : List a) -> l ++ [] = l
appendNilRightNeutral []      = Refl
appendNilRightNeutral (_::xs) = rewrite appendNilRightNeutral xs in Refl

||| Appending lists is associative.
export
appendAssociative : (l, c, r : List a) -> l ++ (c ++ r) = (l ++ c) ++ r
appendAssociative []      c r = Refl
appendAssociative (_::xs) c r = rewrite appendAssociative xs c r in Refl

||| `reverseOnto` reverses the list and prepends it to the "onto" argument
revOnto : (xs, vs : List a) -> reverseOnto xs vs = reverse vs ++ xs
revOnto _ [] = Refl
revOnto xs (v :: vs)
    = rewrite revOnto (v :: xs) vs in
        rewrite appendAssociative (reverse vs) [v] xs in
                                  rewrite revOnto [v] vs in Refl

||| `reverse` is distributive
export
revAppend : (vs, ns : List a) -> reverse ns ++ reverse vs = reverse (vs ++ ns)
revAppend [] ns = rewrite appendNilRightNeutral (reverse ns) in Refl
revAppend (v :: vs) ns
    = rewrite revOnto [v] vs in
        rewrite revOnto [v] (vs ++ ns) in
          rewrite sym (revAppend vs ns) in
            rewrite appendAssociative (reverse ns) (reverse vs) [v] in
              Refl

||| Dropping `m` elements from `l` and then dropping `n` elements from the
||| result, is the same as simply dropping `n+m` elements from `l`
export
dropFusion : (n, m : Nat) -> (l : List t) -> drop n (drop m l) = drop (n+m) l
dropFusion  Z     m    l      = Refl
dropFusion (S n)  Z    l      = rewrite plusZeroRightNeutral n in Refl
dropFusion (S n) (S m) []     = Refl
dropFusion (S n) (S m) (x::l) = rewrite plusAssociative n 1 m in
                                rewrite plusCommutative n 1 in
                                dropFusion (S n) m l

||| Mapping a function over a list does not change the length of the list.
export
lengthMap : (xs : List a) -> length (map f xs) = length xs
lengthMap [] = Refl
lengthMap (x :: xs) = cong S (lengthMap xs)

||| Proof that replicate produces a list of the requested length.
export
lengthReplicate : (n : Nat) -> length (replicate n x) = n
lengthReplicate 0 = Refl
lengthReplicate (S k) = cong S (lengthReplicate k)

export
foldlAppend : (f : acc -> a -> acc) -> (init : acc) -> (xs : List a) -> (ys : List a) -> foldl f init (xs ++ ys) = foldl f (foldl f init xs) ys
foldlAppend f init []      ys = Refl
foldlAppend f init (x::xs) ys = rewrite foldlAppend f (f init x) xs ys in Refl

export
filterAppend : (f : a -> Bool) -> (xs, ys : List a) -> filter f (xs ++ ys) = filter f xs ++ filter f ys
filterAppend f []      ys = Refl
filterAppend f (x::xs) ys with (f x)
  _ | False = rewrite filterAppend f xs ys in Refl
  _ | True  = rewrite filterAppend f xs ys in Refl

export
mapMaybeFusion : (g : b -> Maybe c) -> (f : a -> Maybe b) -> (xs : List a) -> mapMaybe g (mapMaybe f xs) = mapMaybe (f >=> g) xs
mapMaybeFusion g f []      = Refl
mapMaybeFusion g f (x::xs) with (f x)
  _ | Nothing = mapMaybeFusion g f xs
  _ | (Just y) with (g y)
    _ | Nothing = mapMaybeFusion g f xs
    _ | (Just z) = rewrite mapMaybeFusion g f xs in Refl

export
mapMaybeAppend : (f : a -> Maybe b) -> (xs, ys : List a) -> mapMaybe f (xs ++ ys) = mapMaybe f xs ++ mapMaybe f ys
mapMaybeAppend f []      ys = Refl
mapMaybeAppend f (x::xs) ys with (f x)
  _ | Nothing  = rewrite mapMaybeAppend f xs ys in Refl
  _ | (Just y) = rewrite mapMaybeAppend f xs ys in Refl

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (xs : List a) -> map g (map f xs) = map (g . f) xs
mapFusion g f []      = Refl
mapFusion g f (x::xs) = rewrite mapFusion g f xs in Refl

export
mapAppend : (f : a -> b) -> (xs, ys : List a) -> map f (xs ++ ys) = map f xs ++ map f ys
mapAppend f []      ys = Refl
mapAppend f (x::xs) ys = rewrite mapAppend f xs ys in Refl

0 mapTRIsMap :  (f : a -> b) -> (as : List a) -> mapTR f as === map f as
mapTRIsMap f = lemma Lin
  where lemma :  (sb : SnocList b)
              -> (as : List a)
              -> mapAppend sb f as === (sb <>> map f as)
        lemma sb []        = Refl
        lemma sb (x :: xs) = lemma (sb :< f x) xs


0 mapMaybeTRIsMapMaybe :  (f : a -> Maybe b)
                       -> (as : List a)
                       -> mapMaybeTR f as === mapMaybe f as
mapMaybeTRIsMapMaybe f = lemma Lin
  where lemma :  (sb : SnocList b)
              -> (as : List a)
              -> mapMaybeAppend sb f as === (sb <>> mapMaybe f as)
        lemma sb []        = Refl
        lemma sb (x :: xs) with (f x)
          lemma sb (x :: xs) | Nothing = lemma sb xs
          lemma sb (x :: xs) | Just v  = lemma (sb :< v) xs

0 filterTRIsFilter :  (f : a -> Bool)
                   -> (as : List a)
                   -> filterTR f as === filter f as
filterTRIsFilter f = lemma Lin

  where lemma :  (sa : SnocList a)
              -> (as : List a)
              -> filterAppend sa f as === (sa <>> filter f as)
        lemma sa []        = Refl
        lemma sa (x :: xs) with (f x)
          lemma sa (x :: xs) | False = lemma sa xs
          lemma sa (x :: xs) | True  = lemma (sa :< x) xs

0 replicateTRIsReplicate : (n : Nat) -> (x : a) -> replicateTR [] n x === replicate n x
replicateTRIsReplicate n x = trans (lemma [] n) (appendNilRightNeutral _)
  where lemma1 : (as : List a) -> (m : Nat) -> (x :: replicate m x) ++ as === replicate m x ++ (x :: as)
        lemma1 as 0     = Refl
        lemma1 as (S k) = cong (x ::) (lemma1 as k)

        lemma : (as : List a) -> (m : Nat) -> replicateTR as m x === replicate m x ++ as
        lemma as 0     = Refl
        lemma as (S k) =
          let prf := lemma (x :: as) k
           in trans prf (sym $ lemma1 as k)
