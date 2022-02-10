module Data.Linear.LVect

import Data.Fin

import Data.Linear.Bifunctor
import Data.Linear.Interface
import Data.Linear.Notation
import Data.Linear.LNat
import Data.Linear.LList

%default total

public export
data LVect : Nat -> Type -> Type where
  Nil : LVect Z a
  (::) : a -@ LVect n a -@ LVect (S n) a

%name LVect xs, ys, zs, ws

export
lookup : Fin (S n) -@ LVect (S n) a -@ LPair a (LVect n a)
lookup FZ     (v :: vs) = (v # vs)
lookup (FS k) (v :: vs@(_ :: _)) = bimap id (v ::) (lookup k vs)

export
(<$>) : (f : a -@ b) -> LVect n a -@ LVect n b
f <$> [] = []
f <$> x :: xs = f x :: (f <$> xs)

export
pure : {n : Nat} -> a -> LVect n a
pure {n = Z} _ = []
pure {n = S n} x = x :: pure x

export
(<*>) : LVect n (a -@ b) -@ LVect n a -@ LVect n b
[] <*> [] = []
f :: fs <*> x :: xs = f x :: (fs <*> xs)

export
zip : LVect n a -@ LVect n b -@ LVect n (LPair a b)
zip [] [] = []
zip (a :: as) (b :: bs) = (a # b) :: zip as bs

export
unzip : LVect n (LPair a b) -@ LPair (LVect n a) (LVect n b)
unzip [] = [] # []
unzip ((a # b) :: abs) = let (as # bs) = LVect.unzip abs in (a :: as # b :: bs)

export
splitAt : (1 m : Nat) -> LVect (m + n) a -@ LPair (LVect m a) (LVect n a)
splitAt Z as = [] # as
splitAt (S m) (a :: as) = let (xs # ys) = LVect.splitAt m as in (a :: xs # ys)

export
(++) : LVect m a -@ LVect n a -@ LVect (m + n) a
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

export
lfoldr : (0 p : Nat -> Type) -> (forall n. a -@ p n -@ p (S n)) -> p Z -@ LVect n a -@ p n
lfoldr p c n [] = n
lfoldr p c n (x :: xs) = c x (lfoldr p c n xs)

export
lfoldl : (0 p : Nat -> Type) -> (forall n. a -@ p n -@ p (S n)) -> p Z -@ LVect n a -@ p n
lfoldl p c n [] = n
lfoldl p c n (x :: xs) = lfoldl (p . S) c (c x n) xs

export
reverse : LVect m a -@ LVect m a
reverse = lfoldl (\ m => LVect m a) (::) []

export
Consumable a => Consumable (LVect n a) where
  consume [] = ()
  consume (x :: xs) = x `seq` consume xs

export
Duplicable a => Duplicable (LVect n a) where
  duplicate [] = [[], []]
  duplicate (x :: xs) = (::) <$> duplicate x <*> duplicate xs

||| Map a linear vector
export
map : (0 f : a -@ b) -> {auto 1 fns : n `Copies` f} -> LVect n a -@ LVect n b
map f {fns = []} [] = []
map f {fns = f :: fs} (x :: xs) = f x :: map f {fns = fs} xs

||| Extract all
export
length : Consumable a => LVect n a -@ LNat
length [] = Zero
length (x :: xs) = let () = consume x in Succ (length xs)

||| Fold a linear vector.
export
foldl : (0 f : acc -@ a -@ acc) -> {auto 1 fns : n `Copies` f} -> acc -@ (LVect n a) -@ acc
foldl _ {fns = []} acc [] = acc
foldl f {fns = f :: fs} acc (x :: xs) = foldl f {fns = fs} (f acc x) xs

export
replicate : (1 n : LNat) -> (0 v : a) -> {auto 1 vs : toNat n `Copies` v} -> LVect (toNat n) a
replicate Zero v {vs = []} = []
replicate (Succ n) v {vs = (v :: vs)} = v :: replicate n v {vs}

||| Bind a linear vector.
export
(>>=) : LVect n a -@ ((0 f : a -@ LVect m b) -> {1 fns : n `Copies` f} -> LVect (n * m) b)
(>>=) [] _ {fns = []} = []
(>>=) (v :: xs) f {fns = f :: fs} = f v ++ (>>=) {fns = fs} xs f

||| Extract all the copies into a vector of the same length as the number of copies.
export
copiesToVect : {0 v : a} -> n `Copies` v -@ LVect n a
copiesToVect [] = []
copiesToVect (v :: copies) = v :: copiesToVect copies
