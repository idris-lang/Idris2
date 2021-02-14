module Data.Binary.Digit

%default total

||| This is essentially Bool but with names that are easier
||| to understand
public export
data Digit : Type where
  O : Digit
  I : Digit

public export
toNat : Digit -> Nat
toNat O = 0
toNat I = 1
