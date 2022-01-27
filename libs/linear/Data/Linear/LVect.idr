module Data.Linear.LVect

import Data.Linear.Notation
import Data.Linear.Copies
import Data.Linear.LNat
import Data.Linear.LList

%default total

public export
data LVect : Nat -> Type -> Type where
  Nil : LVect Z a
  (::) : a -@ LVect n a -@ LVect (S n) a

%name LVect xs, ys, zs, ws

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
Consumable a => Consumable (LVect n a) where
  consume [] = ()
  consume (x :: xs) = x `seq` consume xs

||| map a linear vector
export
map : (0 f : a -@ b) -> {auto 1 fns : n `Copies` f} -> LVect n a -@ LVect n b
map f {fns=[]} [] = []
map f {fns=(f :: fs)} (x :: xs) = f x :: map f {fns=fs} xs

export
length : Consumable a => LVect n a -@ LNat
length [] = Zero
length (x :: xs) = let () = consume x in Succ (length xs)

export
foldl : {0 f : acc -@ elem -@ acc} -> n `Copies` f -@ acc -@ (LVect n elem) -@ acc
foldl [] acc [] = acc
foldl (f :: fs) acc (x :: xs) = foldl fs (f acc x) xs

export
replicate : (1 n : Nat) -> (0 v : a) -> {auto 1 vs : n `Copies` v} -> LVect n a
replicate 0 v {vs = []} = []
replicate (S n) v {vs = (v :: vs)} = v :: replicate n v {vs}

export
(>>=) : LVect n a -@ ((0 f : a -@ LVect m b) -> {1 fs : n `Copies` f} -> LVect (n * m) b)
(>>=) [] f {fs = []} = []
(>>=) (v :: xs) f {fs = (f :: fs)} = f v ++ (>>=) {fs} xs f

export
copiesToVect : {0 v : a} -> n `Copies` v -@ LVect n a
copiesToVect [] = []
copiesToVect (v :: copies) = v :: copiesToVect copies

