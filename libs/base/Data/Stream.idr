module Data.Stream

import Data.List
import public Data.Zippable

%default total

||| Drop the first n elements from the stream
||| @ n how many elements to drop
public export
drop : (n : Nat) -> Stream a -> Stream a
drop Z     xs = xs
drop (S k) (x::xs) = drop k xs

||| An infinite stream of repetitions of the same thing
public export
repeat : a -> Stream a
repeat x = x :: repeat x

||| Generate an infinite stream by repeatedly applying a function
||| @ f the function to iterate
||| @ x the initial value that will be the head of the stream
public export
iterate : (f : a -> a) -> (x : a) -> Stream a
iterate f x = x :: iterate f (f x)

public export
unfoldr : (b -> (a, b)) -> b -> Stream a
unfoldr f c = let (a, n) = f c in a :: unfoldr f n

||| Get the nth element of a stream
public export
index : Nat -> Stream a -> a
index Z     (x::xs) = x
index (S k) (x::xs) = index k xs

---------------------------
-- Zippable --
---------------------------

export
Zippable Stream where
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

  unzipWith f xs = unzip (map f xs)

  unzip xs = (map fst xs, map snd xs)

  unzipWith3 f xs = unzip3 (map f xs)

  unzip3 xs = (map (\(x, _, _) => x) xs, map (\(_, x, _) => x) xs, map (\(_, _, x) => x) xs)

||| Return the diagonal elements of a stream of streams
export
diag : Stream (Stream a) -> Stream a
diag ((x::xs)::xss) = x :: diag (map tail xss)

||| Produce a Stream of left folds of prefixes of the given Stream
||| @ f the combining function
||| @ acc the initial value
||| @ xs the Stream to process
export
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Stream b) -> Stream a
scanl f acc (x :: xs) = acc :: scanl f (f acc x) xs

||| Produce a Stream repeating a sequence
||| @ xs the sequence to repeat
||| @ ok proof that the list is non-empty
export
cycle : (xs : List a) -> {auto ok : NonEmpty xs} -> Stream a
cycle {a} (x :: xs) {ok = IsNonEmpty} = x :: cycle' xs
  where cycle' : List a -> Stream a
        cycle' []        = x :: cycle' xs
        cycle' (y :: ys) = y :: cycle' ys

public export
partial
takeUntil : (n -> Bool) -> Stream n -> List n
takeUntil p (x :: xs)
    = if p x
         then [x]
         else x :: takeUntil p xs

public export
partial
takeBefore : (n -> Bool) -> Stream n -> List n
takeBefore p (x :: xs)
    = if p x
         then []
         else x :: takeBefore p xs

export
Applicative Stream where
  pure = repeat
  (<*>) = zipWith apply

export
Monad Stream where
  s >>= f = diag (map f s)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

lengthTake : (n : Nat) -> (xs : Stream a) -> length (take n xs) = n
lengthTake Z _ = Refl
lengthTake (S n) (x :: xs) = cong S (lengthTake n xs)
