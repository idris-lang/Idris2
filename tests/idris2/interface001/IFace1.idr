module IFace1

import Stuff

%default partial

infixl 5 ==, /=

interface Eq b where
  (==) : b -> b -> Bool
  (/=) : b -> b -> Bool

Eq Nat where
   (==) Z Z = True
   (==) (S j) (S k) = j == k
   (==) _ _ = False

   (/=) x y = not (x == y)

[silly] Eq Nat where
   (==) Z Z = False
   (==) (S j) (S k) = j == k
   (==) _ _ = True

   (/=) x y = not (x == y)

Eq a => Eq (List a) where
   (==) [] [] = True
   (==) (x :: xs) (y :: ys) = x == y && xs == ys
   (==) _ _ = False

   (/=) x y = not (x == y)

(Eq a, Eq b) => Eq (a, b) where
   (==) (x, y) (x', y') = x == x' && y == y'

   (/=) x y = not (x == y)

[alsoSilly] Eq a => Eq (List a) where
   (==) [] [] = False
   (==) (x :: xs) (y :: ys) = x == y && xs == ys
   (==) _ _ = True

   (/=) x y = not (x == y)

test : ((Eq b, Eq b, Eq a), Eq b) => a -> a -> Bool
test x y = x == y

interface DecEq ty where
  decEq : (x : ty) -> (y : ty) -> Dec (x === y)

-- partial!
eqNat : (x : Nat) -> (y : Nat) -> Dec (x === y)
eqNat (S x) (S y)
    = case eqNat x y of
           Yes Refl => Yes Refl
eqNat Z Z = Yes Refl

DecEq Nat where
  decEq = eqNat

data Vect : _ -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

Eq a => Eq (Vect n a) where
    (==) [] [] = True
    (==) (x :: xs) (y :: ys) = x == y && xs == ys
    (==) _ _ = False

    (/=) xs ys = not (xs == ys)

v1 : DPair Nat (\n => Vect n Nat)
v1 = MkDPair _ [Z, S Z]

v2 : DPair Nat (\n => Vect n Nat)
v2 = MkDPair _ [Z, Z]

(DecEq a, {t : a} -> Eq (p t)) => Eq (DPair a p) where
   (==) (MkDPair l r) (MkDPair l' r')
       = case decEq l l' of
              Yes Refl => ?foo
              No _ => False

   (/=) x y = not (x == y)
