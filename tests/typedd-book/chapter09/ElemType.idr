import Decidable.Equality

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

not_in_nil : Elem value [] -> Void
not_in_nil Here impossible
not_in_nil (There _) impossible

not_in_tail : (notThere : Elem value xs -> Void) -> (notHere : (value = x) -> Void) -> Elem value (x :: xs) -> Void
not_in_tail notThere notHere Here = notHere Refl
not_in_tail notThere notHere (There later) = notThere later

isElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem value [] = No not_in_nil
isElem value (x :: xs) = case decEq value x of
                              Yes Refl => Yes Here
                              No notHere => case isElem value xs of
                                                 Yes prf => Yes (There prf)
                                                 No notThere => No (not_in_tail notThere notHere)
