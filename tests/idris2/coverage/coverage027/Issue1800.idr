import Data.List
import Data.List.Elem
import Decidable.Decidable
import Decidable.Equality

%default covering

toWitness : (prf1 : Dec a) -> IsYes prf1 -> a
toWitness (Yes prf2) x = prf2

data Singleton : {0 k : String} -> k `Elem` ks -> Type where
  Is : (k : String) -> {0 ks : List String} -> {0 prf' : IsYes (k `isElem` ks)}
    -> Singleton (toWitness (isElem k ks) prf')

Example : List String
Example = ["String1", "LongerString", "LastString"]

total
mycase : {0 s : String} -> (0 prf : s `Elem` Example) -> (single : Singleton prf) -> Nat
mycase .(Here) (Is "String1") = 0
mycase .(There $ There Here) (Is "LastString") = 2
mycase %search n impossible
