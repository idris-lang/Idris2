module WithProof0ElabFail

import Language.Reflection

%default total

%language ElabReflection

%hide List.filter

data So : Bool -> Type where
  Oh : So True

eqToSo : b = True -> So b
eqToSo Refl = Oh

data All : (0 p : a -> Type) -> List a -> Type where
  Nil  : All p Nil
  (::) : {0 xs : List a} -> p x -> All p xs -> All p (x :: xs)

filter : (p : a -> Bool) -> (xs : List a) -> List a
filter p [] = []
filter p (x :: xs) with (p x)
  filter p (x :: xs) | False = filter p xs
  filter p (x :: xs) | True = x :: filter p xs

failing "While processing right hand side of with block in allFilter. prf is not accessible in this context"
  %runElab declare `[
    allFilter : (p : a -> Bool) -> (xs : List a) -> All (So . p) (filter p xs)
    allFilter p [] = []
    allFilter p (x :: xs) with (p x) proof 0 prf
      allFilter p (x :: xs) | False = allFilter p xs
      allFilter p (x :: xs) | True = eqToSo prf :: allFilter p xs
  ]
