import Data.Vect

0 foo : {n : Nat} -> {a : Type} -> (u : ()) ->
        case u of () => Vect n a -> Int
foo () [x, y, z] = 1
foo () _ = 2
