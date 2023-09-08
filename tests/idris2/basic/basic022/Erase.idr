myReplace : forall p . (0 rule : x = y) -> (1 val : p y) -> p x
myReplace Refl prf = prf

bad : (0 x : Bool) -> Bool
bad False = True
bad True = False

data LT : Nat -> Nat -> Type where
     LeZ : LT Z (S k)
     LeS : LT j k -> LT (S j) (S k)

-- prf isn't used in the run time case tree, so erasure okay
minus : (x : Nat) -> (y : Nat) -> (0 prf : LT y x) -> Nat
minus (S k) Z LeZ = S k
minus (S k) (S j) (LeS p) = minus k j p

-- y is used in the run time case tree, so erasure not okay
minusBad : (x : Nat) -> (0 y : Nat) -> (0 prf : LT y x) -> Nat
minusBad (S k) Z LeZ = S k
minusBad (S k) (S j) (LeS p) = minusBad k j p

prf : {k : _} -> LT k (S (S k))
prf {k=Z} = LeZ
prf {k=S _} = LeS prf
