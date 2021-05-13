%hide Prelude.integerToNat

data MyNat : Type where
    Z : MyNat
    S : MyNat -> MyNat

%builtin Natural MyNat

integerToMyNat : Integer -> MyNat
integerToMyNat i = if i <= 0
    then Z
    else S $ integerToMyNat (i - 1)

%builtin IntegerToNatural integerToMyNat

natToMyNat : Nat -> MyNat
natToMyNat Z = Z
natToMyNat (S k) = S $ natToMyNat k

%builtin IntegerToNatural natToMyNat

integerToNotNat : Integer -> Maybe String
integerToNotNat x = Just "Boo"

%builtin IntegerToNatural integerToNotNat
