module Data.Binary.Digit

%default total

||| This is essentially Bool but with names that are easier
||| to understand
public export
data Digit : Type where
  O : Digit
  I : Digit

||| Translation to Bool
public export
isI : Digit -> Bool
isI I = True
isI O = False

public export
Cast Digit Nat where
  cast O = 0
  cast I = 1
