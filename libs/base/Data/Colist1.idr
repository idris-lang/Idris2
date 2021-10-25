module Data.Colist1

import Data.Colist
import Data.List
import Data.List1
import Data.Nat
import Data.Stream
import public Data.Zippable

%default total

||| A possibly finite, non-empty Stream.
public export
data Colist1 : (a : Type) -> Type where
  (:::) : a -> Colist a -> Colist1 a

--------------------------------------------------------------------------------
--          Creating Colist1
--------------------------------------------------------------------------------

||| Convert a `List1` to a `Colist1`.
public export
fromList1 : List1 a -> Colist1 a
fromList1 (h ::: t) = h ::: fromList t

||| Convert a stream to a `Colist1`.
public export
fromStream : Stream a -> Colist1 a
fromStream (x :: xs) = x ::: fromStream xs

||| Try to convert a `Colist` to a `Colist1`. Returns `Nothing` if
||| the given `Colist` is empty.
public export
fromColist : Colist a -> Maybe (Colist1 a)
fromColist Nil       = Nothing
fromColist (x :: xs) = Just (x ::: xs)

||| Try to convert a list to a `Colist1`. Returns `Nothing` if
||| the given list is empty.
public export
fromList : List a -> Maybe (Colist1 a)
fromList = fromColist . fromList

||| Create a `Colist1` of only a single element.
public export
singleton : a -> Colist1 a
singleton a = a ::: Nil

||| An infinite `Colist1` of repetitions of the same element.
public export
repeat : a -> Colist1 a
repeat v = v ::: repeat v

||| Create a `Colist1` of `n` replications of the given element.
public export
replicate : (n : Nat) -> {auto 0 prf : IsSucc n} -> a -> Colist1 a
replicate 0     _ impossible
replicate (S k) x = x ::: replicate k x

||| Produce a `Colist1` by repeating a sequence
public export
cycle : List1 a -> Colist1 a
cycle (x ::: xs) = x ::: cycle (xs ++ [x])

||| Generate an infinite `Colist1` by repeatedly applying a function.
public export
iterate : (f : a -> a) -> a -> Colist1 a
iterate f a  = a ::: iterate f (f a)

||| Generate a `Colist1` by repeatedly applying a function.
||| This stops once the function returns `Nothing`.
public export
iterateMaybe : (f : a -> Maybe a) -> a -> Colist1 a
iterateMaybe f a  = a ::: iterateMaybe f (f a)

||| Generate a `Colist1` by repeatedly applying a function
||| to a seed value.
||| This stops once the function returns `Nothing`.
public export
unfold : (f : s -> Maybe (s,a)) -> s -> a -> Colist1 a
unfold f s a = a ::: unfold f s

--------------------------------------------------------------------------------
--          Basic Functions
--------------------------------------------------------------------------------

||| Convert a `Colist1` to a `Colist`
public export
forget : Colist1 a -> Colist a
forget (h ::: t) = h :: t

||| Convert an `Inf (Colist1 a)` to an `Inf (Colist a)`
public export
forgetInf : Inf (Colist1 a) -> Inf (Colist a)
forgetInf (h ::: t) = h :: t

||| Prepends an element to a `Colist1`.
public export
cons : (x : a) -> (xs : Colist1 a) -> Colist1 a
cons x xs = x ::: forget xs

||| Concatenate two `Colist1`s
public export
append : Colist1 a -> Colist1 a -> Colist1 a
append (h ::: t) ys = h ::: append t (forget ys)

||| Append a `Colist1` to a `List`.
public export
lappend : List a -> Colist1 a -> Colist1 a
lappend Nil       ys = ys
lappend (x :: xs) ys = x ::: lappend xs (forget ys)

||| Append a `List` to a `Colist1`.
public export
appendl : Colist1 a -> List a -> Colist1 a
appendl (x ::: xs) ys = x ::: appendl xs ys

||| Take a `Colist1` apart
public export
uncons : Colist1 a -> (a, Colist a)
uncons (h ::: tl) = (h, tl)

||| Extract the first element from a `Colist1`
public export
head : Colist1 a -> a
head (h ::: _) = h

||| Drop the first element from a `Colist1`
public export
tail : Colist1 a -> Colist a
tail (_ ::: t) = t

||| Take up to `n` elements from a `Colist1`
public export
take : (n : Nat) -> {auto 0 prf : IsSucc n} -> Colist1 a -> List1 a
take 0     _          impossible
take (S k) (x ::: xs) = x ::: take k xs

||| Take elements from a `Colist1` up to and including the
||| first element, for which `p` returns `True`.
public export
takeUntil : (p : a -> Bool) -> Colist1 a -> Colist1 a
takeUntil p (x ::: xs) = if p x then singleton x else x ::: takeUntil p xs

||| Take elements from a `Colist1` up to (but not including) the
||| first element, for which `p` returns `True`.
public export
takeBefore : (p : a -> Bool) -> Colist1 a -> Colist a
takeBefore p = takeBefore p . forget

||| Take elements from a `Colist1` while the given predicate `p`
||| returns `True`.
public export
takeWhile : (p : a -> Bool) -> Colist1 a -> Colist a
takeWhile p = takeWhile p . forget

||| Extract all values wrapped in `Just` from the beginning
||| of a `Colist1`. This stops, once the first `Nothing` is encountered.
public export
takeWhileJust : Colist1 (Maybe a) -> Colist a
takeWhileJust = takeWhileJust . forget

||| Drop up to `n` elements from the beginning of the `Colist1`.
public export
drop : (n : Nat) -> Colist1 a -> Colist a
drop n = drop n . forget

||| Try to extract the `n`-th element from a `Colist1`.
public export
index : (n : Nat) -> Colist1 a -> Maybe a
index n = index n . forget

||| Produce a `Colist1` of left folds of prefixes of the given `Colist1`.
||| @ f the combining function
||| @ acc the initial value
||| @ xs the `Colist1` to process
export
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Colist1 b) -> Colist1 a
scanl f acc (x ::: xs) = acc ::: scanl f (f acc x) xs

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export
Semigroup (Colist1 a) where
  (<+>) = append

public export
Functor Colist1 where
  map f (x ::: xs) = f x ::: map f xs

public export
Applicative Colist1 where
  pure = repeat

  (f ::: fs) <*> (a ::: as) = f a ::: (fs <*> as)

public export
Zippable Colist1 where
  zipWith f (x ::: xs) (y ::: ys) = f x y ::: zipWith f xs ys

  zipWith3 f (x ::: xs) (y ::: ys) (z ::: zs) =
    f x y z ::: zipWith3 f xs ys zs

  unzip xs = (map fst xs, map snd xs)

  unzip3 xs = ( map (\(a,_,_) => a) xs
              , map (\(_,b,_) => b) xs
              , map (\(_,_,c) => c) xs
              )

  unzipWith f = unzip . map f

  unzipWith3 f = unzip3 . map f

--------------------------------------------------------------------------------
-- Interleavings
--------------------------------------------------------------------------------

-- zig, zag, and cantor are taken from the paper
-- Applications of Applicative Proof Search
-- by Liam O'Connor

public export
zig : List1 (Colist1 a) -> Colist (Colist1 a) -> Colist a

public export
zag : List1 a -> List (Colist1 a) -> Colist (Colist1 a) -> Colist a

zig xs = zag (head <$> xs) (mapMaybe (fromColist . tail) $ forget xs)

zag (x ::: []) [] [] = x :: []
zag (x ::: []) (z :: zs) [] = x :: zig (z ::: zs) []
zag (x ::: []) zs (l :: ls) = x :: zig (l ::: zs) ls
zag (x ::: (y :: xs)) zs ls = x :: zag (y ::: xs) zs ls

public export
cantor : Colist1 (Colist1 a) -> Colist1 a
cantor (xxs ::: []) = xxs
cantor ((x ::: xs) ::: (yys :: zzss))
  = x ::: zig (yys ::: mapMaybe fromColist [xs]) zzss

namespace Colist

  public export
  cantor : List (Colist a) -> Colist a
  cantor xs =
    let Just (l ::: ls) = List.toList1' $ mapMaybe fromColist xs
          | Nothing => []
    in zig (l ::: []) (fromList ls)

  -- Exploring the (truncated) Nat*Nat top right quadrant of the plane
  -- using Cantor's zig-zag traversal:
  example :
     let nats : Colist Nat; nats = fromStream Stream.nats in
     take 10 (Colist.cantor [ map (0,) nats
                            , map (1,) nats
                            , map (2,) nats
                            , map (3,) nats])
     === [ (0, 0)
         , (1, 0), (0, 1)
         , (2, 0), (1, 1), (0, 2)
         , (3, 0), (2, 1), (1, 2), (0, 3)
         ]
  example = Refl

namespace DPair

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  planeWith : {0 p : a -> Type} ->
              ((x : a) -> p x -> c) ->
              Colist1 a -> ((x : a) -> Colist1 (p x)) ->
              Colist1 c
  planeWith k as f = cantor (map (\ x => map (k x) (f x)) as)

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  plane : {0 p : a -> Type} ->
          Colist1 a -> ((x : a) -> Colist1 (p x)) ->
          Colist1 (x : a ** p x)
  plane = planeWith (\ x, prf => (x ** prf))

namespace Pair

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  planeWith : (a -> b -> c) ->
              Colist1 a -> (a -> Colist1 b) ->
              Colist1 c
  planeWith k as f = cantor (map (\ x => map (k x) (f x)) as)

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  plane : Colist1 a -> (a -> Colist1 b) -> Colist1 (a, b)
  plane = Pair.planeWith (,)

--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

-- Exploring the Nat*Nat top right quadrant of the plane
-- using Cantor's zig-zag traversal:
example :
     let nats1 = fromStream Stream.nats in
     Colist1.take 10 (Pair.plane nats1 (const nats1))
     === (0, 0) :::
         [ (1, 0), (0, 1)
         , (2, 0), (1, 1), (0, 2)
         , (3, 0), (2, 1), (1, 2), (0, 3)
         ]
example = Refl
