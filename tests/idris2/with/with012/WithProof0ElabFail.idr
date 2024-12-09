module WithProof0ElabFail

import Data.So
import Data.List.Quantifiers
import Language.Reflection

%default total

%language ElabReflection

%hide List.filter

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
