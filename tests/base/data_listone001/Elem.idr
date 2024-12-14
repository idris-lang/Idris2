import Data.List
import Data.List.Elem
import Data.List1
import Data.List1.Elem

decHomogeneousElemList : (el1 : Data.List.Elem.Elem x xs) -> (el2 : Data.List.Elem.Elem x xs) -> Dec (el1 === el2)
decHomogeneousElemList Here         Here         = Yes Refl
decHomogeneousElemList (There _)    Here         = No uninhabited
decHomogeneousElemList Here         (There _)    = No uninhabited
decHomogeneousElemList (There el1') (There el2') = case decHomogeneousElemList el1' el2' of
                                                    Yes Refl => Yes Refl
                                                    No contra => No $ \Refl => contra Refl

decHeterogeneousElemList : (el1 : Data.List.Elem.Elem x xs) -> (el2 : Data.List.Elem.Elem y xs) -> Dec (el1 ~=~ el2)
decHeterogeneousElemList Here         Here         = Yes Refl
decHeterogeneousElemList (There _)    Here         = No uninhabited
decHeterogeneousElemList Here         (There _)    = No uninhabited
decHeterogeneousElemList (There el1') (There el2') = case decHeterogeneousElemList el1' el2' of
                                                      Yes Refl => Yes Refl
                                                      No contra => No $ \Refl => contra Refl

decHomogeneousElem : (el1 : Data.List1.Elem.Elem x xs) -> (el2 : Data.List1.Elem.Elem x xs) -> Dec (el1 === el2)
decHomogeneousElem Here         Here         = Yes Refl
decHomogeneousElem (There _)    Here         = No uninhabited
decHomogeneousElem Here         (There _)    = No uninhabited
decHomogeneousElem (There el1') (There el2') = case decHomogeneousElemList el1' el2' of
                                                Yes Refl => Yes Refl
                                                No contra => No $ \Refl => contra Refl

decHomogeneousElem' : (el1 : Data.List1.Elem.Elem x xs) -> (el2 : Data.List1.Elem.Elem x xs) -> Dec (el1 = el2)
decHomogeneousElem' = decHomogeneousElem

decHeterogeneousElem : (el1 : Data.List1.Elem.Elem x xs) -> (el2 : Data.List1.Elem.Elem y xs) -> Dec (el1 ~=~ el2)
decHeterogeneousElem Here         Here         = Yes Refl
decHeterogeneousElem (There _)    Here         = No uninhabited
decHeterogeneousElem Here         (There _)    = No uninhabited
decHeterogeneousElem (There el1') (There el2') = case decHeterogeneousElemList el1' el2' of
                                                  Yes Refl => Yes Refl
                                                  No contra => No $ \Refl => contra Refl

decHeterogeneousElem' : (el1 : Data.List1.Elem.Elem x xs) -> (el2 : Data.List1.Elem.Elem y xs) -> Dec (el1 = el2)
decHeterogeneousElem' = decHeterogeneousElem

main : IO ()
main = printLn "OK"
