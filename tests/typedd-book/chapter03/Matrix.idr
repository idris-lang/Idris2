import Data.Vect

createEmpties : {n : _} -> Vect n (Vect 0 elt)
createEmpties {n = Z} = []
createEmpties {n = (S k)} = [] :: createEmpties

transposeHelper : (x : Vect n elt) -> (xs_trans : Vect n (Vect k elt)) -> Vect n (Vect (S k) elt)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMat : {n : _} -> Vect m (Vect n elt) -> Vect n (Vect m elt)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                             transposeHelper x xsTrans
