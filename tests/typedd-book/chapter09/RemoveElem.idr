import Data.Vect
import Decidable.Equality

removeElem_v1 : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
removeElem_v1 value (x :: xs) = case decEq value x of
                                     Yes prf => xs
                                     No contra => ?removeElem_v1_rhs -- x :: removeElem_v1 value xs

Uninhabited (2 + 2 = 5) where
    uninhabited Refl impossible

{-}
removeElem : (value : a) -> (xs : Vect (S n) a) ->
             Elem value xs ->
             Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later)
                                          = y :: removeElem value ys later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf
-}

removeElem : {n : _} ->
             (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later}
                                          = y :: removeElem value ys

my_elem : Eq a => (value : a) -> (xs : Vect n a) -> Bool
my_elem value [] = False
my_elem value (x :: xs) = case value == x of
                               False => my_elem value xs
                               True => True

not_in_nil : Elem value [] -> Void
not_in_nil Here impossible
not_in_nil (There _) impossible

not_in_tail : (contra1 : Elem value xs -> Void) -> (contra : (value = x) -> Void) -> Elem value (x :: xs) -> Void
not_in_tail contra1 contra Here = contra Refl
not_in_tail contra1 contra (There later) = contra1 later

my_decElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
my_decElem value [] = No not_in_nil
my_decElem value (x :: xs)
      = case decEq value x of
            (Yes Refl) => Yes Here
            (No contra) => case my_decElem value xs of
                                (Yes prf) => Yes (There prf)
                                (No contra1) => No (not_in_tail contra1 contra)
