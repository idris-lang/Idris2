module Data.Vect

import Data.List
import Data.Nat
import public Data.Fin

import Decidable.Equality

%default total

public export
data Vect : (len : Nat) -> (elt : Type) -> Type where
  ||| Empty vector
  Nil  : Vect Z elt
  ||| A non-empty vector of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (1 x : elt) -> (1 xs : Vect len elt) -> Vect (S len) elt

-- Hints for interactive editing
%name Vect xs,ys,zs,ws

public export
length : (xs : Vect len elt) -> Nat
length [] = 0
length (_::xs) = 1 + length xs

||| Show that the length function on vectors in fact calculates the length
export
lengthCorrect : (xs : Vect len elt) -> length xs = len
lengthCorrect []        = Refl
lengthCorrect (_ :: xs) = rewrite lengthCorrect xs in Refl

||| If two vectors are equal, their heads and tails are equal
export
vectInjective : {0 xs : Vect n a} -> {0 ys : Vect m b} -> x::xs = y::ys -> (x = y, xs = ys)
vectInjective Refl = (Refl, Refl)

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

||| All but the first element of the vector
|||
||| ```idris example
||| tail [1,2,3,4]
||| ```
public export
tail : Vect (S len) elt -> Vect len elt
tail (_::xs) = xs

||| Only the first element of the vector
|||
||| ```idris example
||| head [1,2,3,4]
||| ```
public export
head : Vect (S len) elt -> elt
head (x::_) = x

||| The last element of the vector
|||
||| ```idris example
||| last [1,2,3,4]
||| ```
public export
last : Vect (S len) elt -> elt
last [x]        = x
last (_::y::ys) = last $ y::ys

||| All but the last element of the vector
|||
||| ```idris example
||| init [1,2,3,4]
||| ```
public export
init : Vect (S len) elt -> Vect len elt
init [_]        = []
init (x::y::ys) = x :: init (y::ys)

||| Extract the first `n` elements of a Vect.
public export
take : (1 n  : Nat)
    -> (  xs : Vect (n + m) type)
    -> Vect n type
take 0 xs = Nil
take (S k) (x :: xs) = x :: take k xs

||| Extract a particular element from a vector
|||
||| ```idris example
||| index 1 [1,2,3,4]
||| ```
public export
index : Fin len -> Vect len elt -> elt
index FZ     (x::_)  = x
index (FS k) (_::xs) = index k xs

||| Insert an element at a particular index
|||
||| ```idris example
||| insertAt 1 8 [1,2,3,4]
||| ```
public export
insertAt : (1 idx : Fin (S len)) -> (1 x : elt) -> (1 xs : Vect len elt) -> Vect (S len) elt
insertAt FZ     y xs      = y :: xs
insertAt (FS k) y (x::xs) = x :: insertAt k y xs

||| Construct a new vector consisting of all but the indicated element
|||
||| ```idris example
||| deleteAt 1 [1,2,3,4]
||| ```
public export
deleteAt : (1 idx : Fin (S len)) -> Vect (S len) elt -> Vect len elt
deleteAt FZ     (_::xs)        = xs
deleteAt (FS k) [x]            = absurd k
deleteAt (FS k) (x::xs@(_::_)) = x :: deleteAt k xs

||| Replace an element at a particlar index with another
|||
||| ```idris example
||| replaceAt 1 8 [1,2,3,4]
||| ```
public export
replaceAt : Fin len -> elt -> Vect len elt -> Vect len elt
replaceAt FZ     y (_::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

||| Replace the element at a particular index with the result of applying a function to it
||| @ i the index to replace at
||| @ f the update function
||| @ xs the vector to replace in
|||
||| ```idris example
||| updateAt 1 (+10) [1,2,3,4]
||| ```
public export
updateAt : (i : Fin len) -> (f : elt -> elt) -> (xs : Vect len elt) -> Vect len elt
updateAt FZ     f (x::xs) = f x :: xs
updateAt (FS k) f (x::xs) = x :: updateAt k f xs

||| Append two vectors
|||
||| ```idris example
||| [1,2,3,4] ++ [5,6]
||| ```
public export
(++) : (1 xs : Vect m elt) -> (1 ys : Vect n elt) -> Vect (m + n) elt
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

||| Repeate some value some number of times.
|||
||| @ len the number of times to repeat it
||| @ x the value to repeat
|||
||| ```idris example
||| replicate 4 1
||| ```
public export
replicate : (len : Nat) -> (x : elt) -> Vect len elt
replicate Z     _ = []
replicate (S k) x = x :: replicate k x

||| Merge two ordered vectors
|||
||| ```idris example
||| mergeBy compare (fromList [1,3,5]) (fromList [2,3,4,5,6])
||| ```
export
mergeBy : (elt -> elt -> Ordering) -> (xs : Vect n elt) -> (ys : Vect m elt) -> Vect (n + m) elt
mergeBy     _ [] ys = ys
mergeBy {n} _ xs [] = rewrite plusZeroRightNeutral n in xs
mergeBy {n = S k} {m = S k'} order (x :: xs) (y :: ys)
     = case order x y of
            LT => x :: mergeBy order xs (y :: ys)
            _  => rewrite sym (plusSuccRightSucc k k') in
                             y :: mergeBy order (x :: xs) ys

export
merge : Ord elt => Vect n elt -> Vect m elt -> Vect (n + m) elt
merge = mergeBy compare

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

||| Reverse the order of the elements of a vector
|||
||| ```idris example
||| reverse [1,2,3,4]
||| ```
public export
reverse : (1 xs : Vect len elt) -> Vect len elt
reverse xs = go [] xs
  where go : (1 _ : Vect n elt) -> (1 _ : Vect m elt) -> Vect (n+m) elt
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

||| Alternate an element between the other elements of a vector
||| @ sep the element to intersperse
||| @ xs the vector to separate with `sep`
|||
||| ```idris example
||| intersperse 0 [1,2,3,4]
||| ```
export
intersperse : (sep : elt) -> (xs : Vect len elt) -> Vect (len + pred len) elt
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : elt -> Vect n elt -> Vect (n + n) elt
    intersperse'         sep []      = []
    intersperse' {n=S n} sep (x::xs) = rewrite sym $ plusSuccRightSucc n n
                                       in sep :: x :: intersperse' sep xs

--------------------------------------------------------------------------------
-- Conversion from list (toList is provided by Foldable)
--------------------------------------------------------------------------------

public export
toVect : (n : Nat) -> List a -> Maybe (Vect n a)
toVect Z [] = Just []
toVect (S k) (x :: xs)
    = do xs' <- toVect k xs
         pure (x :: xs')
toVect _ _ = Nothing

public export
fromList' : (1 xs : Vect len elt) -> (1 l : List elt) -> Vect (length l + len) elt
fromList' ys [] = ys
fromList' {len} ys (x::xs) =
  rewrite (plusSuccRightSucc (length xs) len) in
  fromList' (x::ys) xs

||| Convert a list to a vector.
|||
||| The length of the list should be statically known.
|||
||| ```idris example
||| fromList [1,2,3,4]
||| ```
public export
fromList : (1 l : List elt) -> Vect (length l) elt
fromList l =
  rewrite (sym $ plusZeroRightNeutral (length l)) in
  reverse $ fromList' [] l

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

||| Combine two equal-length vectors pairwise with some function.
|||
||| @ f the function to combine elements with
||| @ xs the first vector of elements
||| @ ys the second vector of elements
|||
||| ```idris example
||| zipWith (+) (fromList [1,2,3,4]) (fromList [5,6,7,8])
||| ```
public export
zipWith : (f : a -> b -> c) -> (xs : Vect n a) -> (ys : Vect n b) -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Linear version
public export
lzipWith : (f : (1 _ : a) -> (1 _ : b) -> c)
      -> (1 _ : Vect n a)
      -> (1 _ : Vect n b)
      -> Vect n c
lzipWith _ [] [] = []
lzipWith f (x::xs) (y::ys) = f x y :: lzipWith f xs ys

||| Extensional correctness lemma
export
lzipWithSpec : (f : (1 _ : a) -> (1 _ : b) -> c)
         -> (xs : Vect n a) -> (ys : Vect n b)
         -> lzipWith f xs ys = zipWith f xs ys
lzipWithSpec _ [] [] = Refl
lzipWithSpec f (_::xs) (_::ys) = rewrite lzipWithSpec f xs ys in Refl

||| Combine three equal-length vectors into a vector with some function
|||
||| ```idris example
||| zipWith3 (\x,y,z => x+y+z) (fromList [1,2,3,4]) (fromList [5,6,7,8]) (fromList [1,1,1,1])
||| ```
public export
zipWith3 : (a -> b -> c -> d) -> (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n d
zipWith3 f []      []      []      = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Combine two equal-length vectors pairwise
|||
||| ```idris example
||| zip (fromList [1,2,3,4]) (fromList [1,2,3,4])
||| ```
public export
zip : (1 xs : Vect n a) -> (1 ys : Vect n b) -> Vect n (a, b)
zip []      []      = []
zip (x::xs) (y::ys) = (x, y) :: zip xs ys

||| Combine three equal-length vectors elementwise into a vector of tuples
|||
||| ```idris example
||| zip3 (fromList [1,2,3,4]) (fromList [1,2,3,4]) (fromList [1,2,3,4])
||| ```
public export
zip3 : (1 xs : Vect n a) -> (1 ys : Vect n b) -> (1 zs : Vect n c) -> Vect n (a, b, c)
zip3 []      []      []      = []
zip3 (x::xs) (y::ys) (z::zs) = (x, y, z) :: zip3 xs ys zs

||| Convert a vector of pairs to a pair of vectors
|||
||| ```idris example
||| unzip (fromList [(1,2), (1,2)])
||| ```
public export
unzip : (1 xs : Vect n (a, b)) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) = let (lefts, rights) = unzip xs
                     in (l::lefts, r::rights)

||| Convert a vector of three-tuples to a triplet of vectors
|||
||| ```idris example
||| unzip3 (fromList [(1,2,3), (1,2,3)])
||| ```
public export
unzip3 : (1 xs : Vect n (a, b, c)) -> (Vect n a, Vect n b, Vect n c)
unzip3 []            = ([], [], [])
unzip3 ((l,c,r)::xs) = let (lefts, centers, rights) = unzip3 xs
                       in (l::lefts, c::centers, r::rights)

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

public export
Eq a => Eq (Vect n a) where
  (==) []      []      = True
  (==) (x::xs) (y::ys) = x == y && xs == ys

export
DecEq a => DecEq (Vect n a) where
  decEq []      []      = Yes Refl
  decEq (x::xs) (y::ys) with (decEq x y, decEq xs ys)
    decEq (x::xs) (x::xs) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (x::xs) (y::ys) | (No nhd, _) = No $ nhd . fst . vectInjective
    decEq (x::xs) (y::ys) | (_, No ntl) = No $ ntl . snd . vectInjective

--------------------------------------------------------------------------------
-- Order
--------------------------------------------------------------------------------

public export
implementation Ord elt => Ord (Vect len elt) where
  compare []      []      = EQ
  compare (x::xs) (y::ys)
      = case compare x y of
             EQ => compare xs ys
             x => x

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

public export
implementation Functor (Vect n) where
  map f []        = []
  map f (x::xs) = f x :: map f xs

||| Map a partial function across a vector, returning those elements for which
||| the function had a value.
|||
||| The first projection of the resulting pair (ie the length) will always be
||| at most the length of the input vector. This is not, however, guaranteed
||| by the type.
|||
||| @ f the partial function (expressed by returning `Maybe`)
||| @ xs the vector to check for results
|||
||| ```idris example
||| mapMaybe ((find (=='a')) . unpack) (fromList ["abc","ade","bgh","xyz"])
||| ```
export
mapMaybe : (f : a -> Maybe b) -> (xs : Vect len a) -> (m : Nat ** Vect m b)
mapMaybe f []      = (_ ** [])
mapMaybe f (x::xs) =
  let (len ** ys) = mapMaybe f xs
  in case f x of
       Just y  => (S len ** y :: ys)
       Nothing => (  len **      ys)

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

public export
foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> Vect n t -> acc
foldrImpl f e go [] = go e
foldrImpl f e go (x::xs) = foldrImpl f e (go . (f x)) xs

public export
implementation Foldable (Vect n) where
  foldr f e xs = foldrImpl f e id xs

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

||| Flatten a vector of equal-length vectors
|||
||| ```idris example
||| concat [[1,2,3], [4,5,6]]
||| ```
public export
concat : (1 xss : Vect m (Vect n elt)) -> Vect (m * n) elt
concat []      = []
concat (v::vs) = v ++ Vect.concat vs

||| Foldr without seeding the accumulator
|||
||| ```idris example
||| foldr1 (-) (fromList [1,2,3])
||| ```
public export
foldr1 : (t -> t -> t) -> Vect (S n) t -> t
foldr1 f [x]        = x
foldr1 f (x::y::xs) = f x (foldr1 f (y::xs))

||| Foldl without seeding the accumulator
|||
||| ```idris example
||| foldl1 (-) (fromList [1,2,3])
||| ```
public export
foldl1 : (t -> t -> t) -> Vect (S n) t -> t
foldl1 f (x::xs) = foldl f x xs
--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

||| The scanl function is similar to foldl, but returns all the intermediate
||| accumulator states in the form of a vector.
|||
||| ```idris example
||| scanl (-) 0 (fromList [1,2,3])
||| ```
public export
scanl : (res -> elt -> res) -> res -> Vect len elt -> Vect (S len) res
scanl f q []      = [q]
scanl f q (x::xs) = q :: scanl f (f q x) xs

||| The scanl1 function is a variant of scanl that doesn't require an explicit
||| starting value.
||| It assumes the first element of the vector to be the starting value and then
||| starts the fold with the element following it.
|||
||| ```idris example
||| scanl1 (-) (fromList [1,2,3])
||| ```
public export
scanl1 : (elt -> elt -> elt) -> Vect len elt -> Vect len elt
scanl1 f [] = []
scanl1 f (x::xs) = scanl f x xs

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Search for an item using a user-provided test
||| @ p the equality test
||| @ e the item to search for
||| @ xs the vector to search in
|||
||| ```idris example
||| elemBy (==) 2 [1,2,3,4]
||| ```
public export
elemBy : (p : elt -> elt -> Bool) -> (e : elt) -> (xs : Vect len elt) -> Bool
elemBy p e []      = False
elemBy p e (x::xs) = p e x || elemBy p e xs

||| Use the default Boolean equality on elements to search for an item
||| @ x what to search for
||| @ xs where to search
|||
||| ```idris example
||| elem 3 [1,2,3,4]
||| ```
public export
elem : Eq elt => (x : elt) -> (xs : Vect len elt) -> Bool
elem = elemBy (==)

||| Find the association of some key with a user-provided comparison
||| @ p the comparison operator for keys (True if they match)
||| @ e the key to look for
|||
||| ```idris example
||| lookupBy (==) 2 [(1, 'a'), (2, 'b'), (3, 'c')]
||| ```
public export
lookupBy : (p : key -> key -> Bool) -> (e : key) -> (xs : Vect n (key, val)) -> Maybe val
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) = if p e l then Just r else lookupBy p e xs

||| Find the assocation of some key using the default Boolean equality test
|||
||| ```idris example
||| lookup 3 [(1, 'a'), (2, 'b'), (3, 'c')]
||| ```
public export
lookup : Eq key => key -> Vect n (key, val) -> Maybe val
lookup = lookupBy (==)

||| Check if any element of xs is found in elts by a user-provided comparison
||| @ p the comparison operator
||| @ elts the vector to search
||| @ xs what to search for
|||
||| ```idris example
||| hasAnyBy (==) [2,5] [1,2,3,4]
||| ```
public export
hasAnyBy : (p : elt -> elt -> Bool) -> (elts : Vect m elt) -> (xs : Vect len elt) -> Bool
hasAnyBy p elts []      = False
hasAnyBy p elts (x::xs) = elemBy p x elts || hasAnyBy p elts xs

||| Check if any element of xs is found in elts using the default Boolean equality test
|||
||| ```idris example
||| hasAny [2,5] [1,2,3,4]
||| ```
public export
hasAny : Eq elt => Vect m elt -> Vect len elt -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

||| Find the first element of the vector that satisfies some test
||| @ p the test to satisfy
|||
||| ```idris example
||| find (== 3) [1,2,3,4]
||| ```
public export
find : (p : elt -> Bool) -> (xs : Vect len elt) -> Maybe elt
find p []      = Nothing
find p (x::xs) = if p x then Just x else find p xs

||| Find the index of the first element of the vector that satisfies some test
|||
||| ```idris example
||| findIndex (== 3) [1,2,3,4]
||| ```
public export
findIndex : (elt -> Bool) -> Vect len elt -> Maybe (Fin len)
findIndex p []        = Nothing
findIndex p (x :: xs) = if p x then Just FZ else map FS (findIndex p xs)

||| Find the indices of all elements that satisfy some test
|||
||| ```idris example
||| findIndices (< 3) [1,2,3,4]
||| ```
public export
findIndices : (elt -> Bool) -> Vect m elt -> List (Fin m)
findIndices p []        = []
findIndices p (x :: xs)
     = let is = map FS $ findIndices p xs in
           if p x then FZ :: is else is

||| Find the index of the first element of the vector that satisfies some test
|||
||| ```idris example
||| elemIndexBy (==) 3 [1,2,3,4]
||| ```
public export
elemIndexBy : (elt -> elt -> Bool) -> elt -> Vect m elt -> Maybe (Fin m)
elemIndexBy p e = findIndex $ p e

||| Find the index of the first element of the vector equal to the given one.
|||
||| ```idris example
||| elemIndex 3 [1,2,3,4]
||| ```
public export
elemIndex : Eq elt => elt -> Vect m elt -> Maybe (Fin m)
elemIndex = elemIndexBy (==)

||| Find the indices of all elements that satisfy some test
|||
||| ```idris example
||| elemIndicesBy (<=) 3 [1,2,3,4]
||| ```
public export
elemIndicesBy : (elt -> elt -> Bool) -> elt -> Vect m elt -> List (Fin m)
elemIndicesBy p e = findIndices $ p e

||| Find the indices of all elements uquals to the given one
|||
||| ```idris example
||| elemIndices 3 [1,2,3,4,3]
||| ```
public export
elemIndices : Eq elt => elt -> Vect m elt -> List (Fin m)
elemIndices = elemIndicesBy (==)

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

||| Find all elements of a vector that satisfy some test
|||
||| ```idris example
||| filter (< 3) (fromList [1,2,3,4])
||| ```
public export
filter : (elt -> Bool) -> Vect len elt -> (p ** Vect p elt)
filter p []      = ( _ ** [] )
filter p (x::xs) =
  let (_ ** tail) = filter p xs
   in if p x then
        (_ ** x::tail)
      else
        (_ ** tail)

||| Make the elements of some vector unique by some test
|||
||| ```idris example
||| nubBy (==) (fromList [1,2,2,3,4,4])
||| ```
public export
nubBy : (elt -> elt -> Bool) -> Vect len elt -> (p ** Vect p elt)
nubBy = nubBy' []
  where
    nubBy' : forall len . Vect m elt -> (elt -> elt -> Bool) -> Vect len elt -> (p ** Vect p elt)
    nubBy' acc p []      = (_ ** [])
    nubBy' acc p (x::xs) with (elemBy p x acc)
      nubBy' acc p (x :: xs) | True  = nubBy' acc p xs
      nubBy' acc p (x :: xs) | False with (nubBy' (x::acc) p xs)
        nubBy' acc p (x :: xs) | False | (_ ** tail) = (_ ** x::tail)

||| Make the elements of some vector unique by the default Boolean equality
|||
||| ```idris example
||| nub (fromList [1,2,2,3,4,4])
||| ```
public export
nub : Eq elt => Vect len elt -> (p ** Vect p elt)
nub = nubBy (==)

||| Delete first element from list according to some test
|||
||| ```idris example
||| deleteBy (<) 3 (fromList [1,2,2,3,4,4])
||| ```
public export
deleteBy : {len : _} -> -- needed for the dependent pair
           (elt -> elt -> Bool) -> elt -> Vect len elt -> (p ** Vect p elt)
deleteBy _  _ []      = (_ ** [])
deleteBy eq x (y::ys) =
  let (len ** zs) = deleteBy eq x ys
  in if x `eq` y then (_ ** ys) else (S len ** y ::zs)

||| Delete first element from list equal to the given one
|||
||| ```idris example
||| delete 2 (fromList [1,2,2,3,4,4])
||| ```
public export
delete : {len : _} ->
         Eq elt => elt -> Vect len elt -> (p ** Vect p elt)
delete = deleteBy (==)

--------------------------------------------------------------------------------
-- Splitting and breaking lists
--------------------------------------------------------------------------------

||| A tuple where the first element is a `Vect` of the `n` first elements and
||| the second element is a `Vect` of the remaining elements of the original.
||| It is equivalent to `(take n xs, drop n xs)` (`splitAtTakeDrop`),
||| but is more efficient.
|||
||| @ n   the index to split at
||| @ xs  the `Vect` to split in two
|||
||| ```idris example
||| splitAt 2 (fromList [1,2,3,4])
||| ```
public export
splitAt : (n : Nat) -> (xs : Vect (n + m) elt) -> (Vect n elt, Vect m elt)
splitAt Z xs = ([], xs)
splitAt (S k) (x :: xs) with (splitAt k {m} xs)
  splitAt (S k) (x :: xs) | (tk, dr) = (x :: tk, dr)

||| A tuple where the first element is a `Vect` of the `n` elements passing given test
||| and the second element is a `Vect` of the remaining elements of the original.
|||
||| ```idris example
||| partition (== 2) (fromList [1,2,3,2,4])
||| ```
public export
partition : (elt -> Bool) -> Vect len elt -> ((p ** Vect p elt), (q ** Vect q elt))
partition p []      = ((_ ** []), (_ ** []))
partition p (x::xs) =
  let ((leftLen ** lefts), (rightLen ** rights)) = partition p xs in
    if p x then
      ((S leftLen ** x::lefts), (rightLen ** rights))
    else
      ((leftLen ** lefts), (S rightLen ** x::rights))

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

||| Verify vector prefix
|||
||| ```idris example
||| isPrefixOfBy (==) (fromList [1,2]) (fromList [1,2,3,4])
||| ```
public export
isPrefixOfBy : (elt -> elt -> Bool) -> Vect m elt -> Vect len elt -> Bool
isPrefixOfBy p [] right        = True
isPrefixOfBy p left []         = False
isPrefixOfBy p (x::xs) (y::ys) = p x y && isPrefixOfBy p xs ys

||| Verify vector prefix
|||
||| ```idris example
||| isPrefixOf (fromList [1,2]) (fromList [1,2,3,4])
||| ```
public export
isPrefixOf : Eq elt => Vect m elt -> Vect len elt -> Bool
isPrefixOf = isPrefixOfBy (==)

||| Verify vector suffix
|||
||| ```idris example
||| isSuffixOfBy (==) (fromList [3,4]) (fromList [1,2,3,4])
||| ```
public export
isSuffixOfBy : (elt -> elt -> Bool) -> Vect m elt -> Vect len elt -> Bool
isSuffixOfBy p left right = isPrefixOfBy p (reverse left) (reverse right)

||| Verify vector suffix
|||
||| ```idris example
||| isSuffixOf (fromList [3,4]) (fromList [1,2,3,4])
||| ```
public export
isSuffixOf : Eq elt => Vect m elt -> Vect len elt -> Bool
isSuffixOf = isSuffixOfBy (==)

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

||| Convert Maybe type into Vect
|||
||| ```idris example
||| maybeToVect (Just 2)
||| ```
public export
maybeToVect : Maybe elt -> (p ** Vect p elt)
maybeToVect Nothing  = (_ ** [])
maybeToVect (Just j) = (_ ** [j])

||| Convert first element of Vect (if exists) into Maybe.
|||
||| ```idris example
||| vectToMaybe [2]
||| ```
public export
vectToMaybe : Vect len elt -> Maybe elt
vectToMaybe []      = Nothing
vectToMaybe (x::xs) = Just x

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

||| Filter out Nothings from Vect and unwrap the Justs
|||
||| ```idris example
||| catMaybes [Just 1, Just 2, Nothing, Nothing, Just 5]
||| ```
public export
catMaybes : (1 xs : Vect n (Maybe elt)) -> (p ** Vect p elt)
catMaybes []             = (_ ** [])
catMaybes (Nothing::xs)  = catMaybes xs
catMaybes ((Just j)::xs) =
  let (_ ** tail) = catMaybes xs
   in (_ ** j::tail)

||| Get diagonal elements
|||
||| ```idris example
||| diag [[1,2,3], [4,5,6], [7,8,9]]
||| ```
public export
diag : Vect len (Vect len elt) -> Vect len elt
diag []             = []
diag ((x::xs)::xss) = x :: diag (map tail xss)

public export
range : {len : Nat} -> Vect len (Fin len)
range {len=Z}   = []
range {len=S _} = FZ :: map FS range

--------------------------------------------------------------------------------
-- Matrix transposition
--------------------------------------------------------------------------------
||| Transpose a `Vect` of `Vect`s, turning rows into columns and vice versa.
|||
||| This is like zipping all the inner `Vect`s together and is equivalent to `traverse id` (`transposeTraverse`).
|||
||| As the types ensure rectangularity, this is an involution, unlike `Prelude.List.transpose`.
|||
||| ```idris example
||| transpose [[1,2], [3,4], [5,6], [7,8]]
||| ```
public export
transpose : {n : _} -> (1 array : Vect m (Vect n elt)) -> Vect n (Vect m elt)
transpose []        = replicate _ []                 -- = [| [] |]
transpose (x :: xs) = lzipWith (::) x (transpose xs) -- = [| x :: xs |]

||| A recursive (non-linear) implementation of transpose
||| Easier for inductive reasoning
public export
transpose' : {n : Nat} -> (xss : Vect m (Vect n x)) -> Vect n (Vect m x)
transpose' []          = replicate _ []
transpose' (xs :: xss) = zipWith (::) xs (transpose' xss)

||| Extensional correctness lemma
export
transposeSpec : {n : Nat} -> (xss : Vect m (Vect n x)) -> transpose xss = transpose' xss
transposeSpec [] = Refl
transposeSpec (y :: xs) = rewrite transposeSpec xs in
                          lzipWithSpec (::) _ _

--------------------------------------------------------------------------------
-- Applicative/Monad/Traversable
--------------------------------------------------------------------------------
-- These only work if the length is known at run time!

public export
implementation {k : Nat} -> Applicative (Vect k) where
    pure = replicate _
    fs <*> vs = zipWith apply fs vs

-- ||| This monad is different from the List monad, (>>=)
-- ||| uses the diagonal.
implementation {k : Nat} -> Monad (Vect k) where
    m >>= f = diag (map f m)

public export
implementation Traversable (Vect k) where
    traverse f []        = pure []
    traverse f (x :: xs) = [| f x :: traverse f xs |]

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

export
implementation Show elt => Show (Vect len elt) where
    show = show . toList

-- Some convenience functions for testing lengths

-- Needs to be Maybe rather than Dec, because if 'n' is unequal to m, we
-- only know we don't know how to make a Vect n a, not that one can't exist.
export
exactLength : {m : Nat} -> -- expected at run-time
              (len : Nat) -> (xs : Vect m a) -> Maybe (Vect len a)
exactLength {m} len xs with (decEq m len)
  exactLength {m = m} m xs | (Yes Refl) = Just xs
  exactLength {m = m} len xs | (No contra) = Nothing

||| If the given Vect is at least the required length, return a Vect with
||| at least that length in its type, otherwise return Nothing
||| @len the required length
||| @xs the vector with the desired length
export
overLength : {m : Nat} -> -- expected at run-time
             (len : Nat) -> (xs : Vect m a) -> Maybe (p ** Vect (plus p len) a)
overLength {m} n xs with (cmp m n)
  overLength {m = m} (plus m (S y)) xs | (CmpLT y) = Nothing
  overLength {m = m} m xs | CmpEQ
         = Just (0 ** xs)
  overLength {m = plus n (S x)} n xs | (CmpGT x)
         = Just (S x ** rewrite plusCommutative (S x) n in xs)
