import Data.Vect

insert : Ord elt => (x : elt) -> (xsSorted : Vect k elt) -> Vect (S k) elt
insert x [] = [x]
insert x (y :: xs) = case x < y of
                          False => y :: insert x xs
                          True => x :: y :: xs

insSort : Ord elt => Vect n elt -> Vect n elt
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in
                        insert x xsSorted
