module Data.List

import Data.Nat
import Data.List1

public export
isNil : List a -> Bool
isNil [] = True
isNil _  = False

public export
isCons : List a -> Bool
isCons [] = False
isCons _  = True

public export
snoc : List a -> a -> List a
snoc xs x = xs ++ [x]

public export
take : Nat -> List a -> List a
take (S k) (x :: xs) = x :: take k xs
take _ _ = []

public export
drop : (n : Nat) -> (xs : List a) -> List a
drop Z     xs      = xs
drop (S n) []      = []
drop (S n) (_::xs) = drop n xs

||| Satisfiable if `k` is a valid index into `xs`
|||
||| @ k the potential index
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

||| Decide whether `k` is a valid index into `xs`
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
index : (n : Nat) -> (xs : List a) -> {auto ok : InBounds n xs} -> a
index Z (x :: xs) {ok = InFirst} = x
index (S k) (_ :: xs) {ok = InLater _} = index k xs

||| Generate a list by repeatedly applying a partial function until exhausted.
||| @ f the function to iterate
||| @ x the initial value that will be the head of the list
public export
iterate : (f : a -> Maybe a) -> (x : a) -> List a
iterate f x  = x :: case f x of
  Nothing => []
  Just y => iterate f y

public export
takeWhile : (p : a -> Bool) -> List a -> List a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (p : a -> Bool) -> List a -> List a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

public export
filter : (p : a -> Bool) -> List a -> List a
filter p [] = []
filter p (x :: xs)
   = if p x
        then x :: filter p xs
        else filter p xs

||| Find the first element of the list that satisfies the predicate.
public export
find : (p : a -> Bool) -> (xs : List a) -> Maybe a
find p [] = Nothing
find p (x::xs) = if p x then Just x else find p xs

||| Find associated information in a list using a custom comparison.
public export
lookupBy : (a -> a -> Bool) -> a -> List (a, b) -> Maybe b
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

||| Check if something is a member of a list using a custom comparison.
public export
elemBy : (a -> a -> Bool) -> a -> List a -> Bool
elemBy p e []      = False
elemBy p e (x::xs) = p e x || elemBy p e xs

public export
nubBy : (a -> a -> Bool) -> List a -> List a
nubBy = nubBy' []
  where
    nubBy' : List a -> (a -> a -> Bool) -> List a -> List a
    nubBy' acc p []      = []
    nubBy' acc p (x::xs) =
      if elemBy p x acc then
        nubBy' acc p xs
      else
        x :: nubBy' (x::acc) p xs

||| O(n^2). The nub function removes duplicate elements from a list. In
||| particular, it keeps only the first occurrence of each element. It is a
||| special case of nubBy, which allows the programmer to supply their own
||| equality test.
|||
||| ```idris example
||| nub (the (List _) [1,2,1,3])
||| ```
public export
nub : Eq a => List a -> List a
nub = nubBy (==)

||| The deleteBy function behaves like delete, but takes a user-supplied equality predicate.
public export
deleteBy : (a -> a -> Bool) -> a -> List a -> List a
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

public export
spanBy : (a -> Maybe b) -> List a -> (List b, List a)
spanBy p [] = ([], [])
spanBy p (x :: xs) = case p x of
  Nothing => ([], x :: xs)
  Just y => let (ys, zs) = spanBy p xs in (y :: ys, zs)

public export
span : (a -> Bool) -> List a -> (List a, List a)
span p []      = ([], [])
span p (x::xs) =
  if p x then
    let (ys, zs) = span p xs in
        (x::ys, zs)
  else
    ([], x::xs)

public export
break : (a -> Bool) -> List a -> (List a, List a)
break p xs = span (not . p) xs

public export
split : (a -> Bool) -> List a -> List1 (List a)
split p xs =
  case break p xs of
    (chunk, [])          => singleton chunk
    (chunk, (c :: rest)) => cons chunk (split p (assert_smaller xs rest))

public export
splitAt : (n : Nat) -> (xs : List a) -> (List a, List a)
splitAt Z xs = ([], xs)
splitAt (S k) [] = ([], [])
splitAt (S k) (x :: xs)
      = let (tk, dr) = splitAt k xs in
            (x :: tk, dr)

public export
partition : (a -> Bool) -> List a -> (List a, List a)
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

||| Replaces all occurences of the first argument with the second argument in a list.
|||
||| ```idris example
||| replaceOn '-' ',' ['1', '-', '2', '-', '3']
||| ```
|||
public export
replaceOn : Eq a => a -> a -> List a -> List a
replaceOn a b l = map (\c => if c == a then b else c) l

public export
reverseOnto : List a -> List a -> List a
reverseOnto acc [] = acc
reverseOnto acc (x::xs) = reverseOnto (x::acc) xs

public export
reverse : List a -> List a
reverse = reverseOnto []

||| Construct a list with `n` copies of `x`.
||| @ n how many copies
||| @ x the element to replicate
public export
replicate : (n : Nat) -> (x : a) -> List a
replicate Z     _ = []
replicate (S n) x = x :: replicate n x

||| Compute the intersect of two lists by user-supplied equality predicate.
export
intersectBy : (a -> a -> Bool) -> List a -> List a -> List a
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

||| Compute the intersect of two lists according to the `Eq` implementation for the elements.
export
intersect : Eq a => List a -> List a -> List a
intersect = intersectBy (==)

export
intersectAllBy : (a -> a -> Bool) -> List (List a) -> List a
intersectAllBy eq [] = []
intersectAllBy eq (xs :: xss) = filter (\x => all (elemBy eq x) xss) xs

export
intersectAll : Eq a => List (List a) -> List a
intersectAll = intersectAllBy (==)

||| Combine two lists elementwise using some function.
|||
||| If the lists are different lengths, the result is truncated to the
||| length of the shortest list.
export
zipWith : (a -> b -> c) -> List a -> List b -> List c
zipWith _ [] _ = []
zipWith _ _ [] = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Combine two lists elementwise into pairs.
|||
||| If the lists are different lengths, the result is truncated to the
||| length of the shortest list.
export
zip : List a -> List b -> List (a, b)
zip = zipWith \x, y => (x, y)

export
zipWith3 : (a -> b -> c -> d) -> List a -> List b -> List c -> List d
zipWith3 _ [] _ _ = []
zipWith3 _ _ [] _ = []
zipWith3 _ _ _ [] = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Combine three lists elementwise into tuples.
|||
||| If the lists are different lengths, the result is truncated to the
||| length of the shortest list.
export
zip3 : List a -> List b -> List c -> List (a, b, c)
zip3 = zipWith3 \x, y, z => (x, y, z)

public export
data NonEmpty : (xs : List a) -> Type where
    IsNonEmpty : NonEmpty (x :: xs)

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
last (_::x::xs) = List.last (x::xs)

||| Return all but the last element of a non-empty list.
||| @ ok proof the list is non-empty
public export
init : (l : List a) -> {auto 0 ok : NonEmpty l} -> List a
init [] impossible
init [_] = []
init (x::y::ys) = x :: init (y::ys)

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

||| Convert any Foldable structure to a list.
export
toList : Foldable t => t a -> List a
toList = foldr (::) []

||| Prefix every element in the list with the given element
|||
||| ```idris example
||| with List (mergeReplicate '>' ['a', 'b', 'c', 'd', 'e'])
||| ```
|||
export
mergeReplicate : a -> List a -> List a
mergeReplicate sep []      = []
mergeReplicate sep (y::ys) = sep :: y :: mergeReplicate sep ys


||| Insert some separator between the elements of a list.
|||
||| ````idris example
||| with List (intersperse ',' ['a', 'b', 'c', 'd', 'e'])
||| ````
|||
export
intersperse : a -> List a -> List a
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

||| Apply a partial function to the elements of a list, keeping the ones at which
||| it is defined.
public export
mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f []      = []
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just j  => j :: mapMaybe f xs

||| Extract all of the values contained in a List of Maybes
public export
catMaybes : List (Maybe a) -> List a
catMaybes = mapMaybe id

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

||| Foldl a non-empty list without seeding the accumulator.
||| @ ok proof that the list is non-empty
public export
foldl1 : (a -> a -> a) -> (l : List a)  -> {auto 0 ok : NonEmpty l} -> a
foldl1 f [] impossible
foldl1 f (x::xs) = foldl f x xs

||| Foldr a non-empty list without seeding the accumulator.
||| @ ok proof that the list is non-empty
public export
foldr1 : (a -> a -> a) -> (l : List a)  -> {auto 0 ok : NonEmpty l} -> a
foldr1 f [] impossible
foldr1 f [x] = x
foldr1 f (x::y::ys) = f x (List.foldr1 f (y::ys))

||| Foldl without seeding the accumulator. If the list is empty, return `Nothing`.
public export
foldl1' : (a -> a -> a) -> List a -> Maybe a
foldl1' f [] = Nothing
foldl1' f xs@(_::_) = Just (List.foldl1 f xs)

||| Foldr without seeding the accumulator. If the list is empty, return `Nothing`.
public export
foldr1' : (a -> a -> a) -> List a -> Maybe a
foldr1' f [] = Nothing
foldr1' f xs@(_::_) = Just (List.foldr1 f xs)

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

export
isPrefixOfBy : (eq : a -> a -> Bool) -> (left, right : List a) -> Bool
isPrefixOfBy p [] _            = True
isPrefixOfBy p _ []            = False
isPrefixOfBy p (x::xs) (y::ys) = p x y && isPrefixOfBy p xs ys

||| The isPrefixOf function takes two lists and returns True iff the first list is a prefix of the second.
export
isPrefixOf : Eq a => List a -> List a -> Bool
isPrefixOf = isPrefixOfBy (==)

export
isSuffixOfBy : (a -> a -> Bool) -> List a -> List a -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

||| The isSuffixOf function takes two lists and returns True iff the first list is a suffix of the second.
export
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
export
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

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

export
Uninhabited ([] = Prelude.(::) x xs) where
  uninhabited Refl impossible

export
Uninhabited (Prelude.(::) x xs = []) where
  uninhabited Refl impossible

||| (::) is injective
export
consInjective : forall x, xs, y, ys .
                the (List a) (x :: xs) = the (List b) (y :: ys) -> (x = y, xs = ys)
consInjective Refl = (Refl, Refl)

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

revOnto : (xs, vs : List a) -> reverseOnto xs vs = reverse vs ++ xs
revOnto _ [] = Refl
revOnto xs (v :: vs)
    = rewrite revOnto (v :: xs) vs in
        rewrite appendAssociative (reverse vs) [v] xs in
                                  rewrite revOnto [v] vs in Refl

export
revAppend : (vs, ns : List a) -> reverse ns ++ reverse vs = reverse (vs ++ ns)
revAppend [] ns = rewrite appendNilRightNeutral (reverse ns) in Refl
revAppend (v :: vs) ns
    = rewrite revOnto [v] vs in
        rewrite revOnto [v] (vs ++ ns) in
          rewrite sym (revAppend vs ns) in
            rewrite appendAssociative (reverse ns) (reverse vs) [v] in
              Refl

export
dropFusion : (n, m : Nat) -> (l : List t) -> drop n (drop m l) = drop (n+m) l
dropFusion  Z     m    l      = Refl
dropFusion (S n)  Z    l      = rewrite plusZeroRightNeutral n in Refl
dropFusion (S n) (S m) []     = Refl
dropFusion (S n) (S m) (x::l) = rewrite plusAssociative n 1 m in
                                rewrite plusCommutative n 1 in
                                dropFusion (S n) m l

export
lengthMap : (xs : List a) -> length (map f xs) = length xs
lengthMap [] = Refl
lengthMap (x :: xs) = cong S (lengthMap xs)
