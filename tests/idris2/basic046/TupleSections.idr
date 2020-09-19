import Data.Vect

distrL : a -> List b -> List (a, b)
distrL a = map (a,)

distrR : b -> List a -> List (a, b)
distrR b = map (, b)

-- closeVect : List (n ** Vect n Nat)
-- closeVect = map (** flip replicate 3) [0..10]

insert : List (Nat,Nat,Nat,Nat)
insert = map (\ f => f (the Nat 0) (the Nat 1))
         [(,,2,3), (2,,,3), (2,3,,)]
