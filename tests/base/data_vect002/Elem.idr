import Data.Vect
import Data.Vect.Elem

decHomogeneousElem : (el1 : Elem x xs) -> (el2 : Elem x xs) -> Dec (el1 === el2)
decHomogeneousElem Here         Here         = Yes Refl
decHomogeneousElem (There _)    Here         = No uninhabited
decHomogeneousElem Here         (There _)    = No uninhabited
decHomogeneousElem (There el1') (There el2') = case decHomogeneousElem el1' el2' of
                                                Yes Refl => Yes Refl
                                                No contra => No $ \Refl => contra Refl

decHomogeneousElem' : (el1 : Elem x xs) -> (el2 : Elem x xs) -> Dec (el1 = el2)
decHomogeneousElem' = decHomogeneousElem

decHeterogeneousElem : (el1 : Elem x xs) -> (el2 : Elem y xs) -> Dec (el1 ~=~ el2)
decHeterogeneousElem Here         Here         = Yes Refl
decHeterogeneousElem (There _)    Here         = No uninhabited
decHeterogeneousElem Here         (There _)    = No uninhabited
decHeterogeneousElem (There el1') (There el2') = case decHeterogeneousElem el1' el2' of
                                                  Yes Refl => Yes Refl
                                                  No contra => No $ \Refl => contra Refl

decHeterogeneousElem' : (el1 : Elem x xs) -> (el2 : Elem y xs) -> Dec (el1 = el2)
decHeterogeneousElem' = decHeterogeneousElem

main : IO ()
main = printLn "OK"
