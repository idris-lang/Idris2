module Data.Linear.LVect

import Data.Linear.Notation

%default total

public export
data LVect : Nat -> Type -> Type where
  Nil : LVect Z a
  (::) : a -@ LVect n a -@ LVect (S n) a

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
unzip ((a # b) :: abs) = let (as # bs) = unzip abs in (a :: as # b :: bs)

export
splitAt : (1 m : Nat) -> LVect (m + n) a -@ LPair (LVect m a) (LVect n a)
splitAt Z as = [] # as
splitAt (S m) (a :: as) = let (xs # ys) = splitAt m as in (a :: xs # ys)

export
(++) : LVect m a -@ LVect n a -@ LVect (m + n) a
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

export
Consumable a => Consumable (LVect n a) where
  consume [] = ()
  consume (x :: xs) = x `seq` consume xs
