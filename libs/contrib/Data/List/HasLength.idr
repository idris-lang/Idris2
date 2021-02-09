module Data.List.HasLength

%default total

||| This relation witnesses the fact a natural number is the length
||| of a list. Unlike a proof that `length xs === n`, it can be easily
||| inverted.
||| It is meant to be used in a runtime-irrelevant fashion.
public export
data HasLength : Nat -> List a -> Type where
  Z : HasLength Z []
  S : HasLength n xs -> HasLength (S n) (x :: xs)

||| This specification corresponds to the length function
public export
%hint
hasLength : (xs : List a) -> HasLength (length xs) xs
hasLength [] = Z
hasLength (_ :: xs) = S (hasLength xs)
