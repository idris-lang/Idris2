import Data.Fin
import Data.Vect

tail : (Fin (S n) -> a) -> (Fin n -> a)
tail f = f . FS

toVectFun : {n : Nat} -> (Fin n -> a) -> Vect n a
toVectFun {n =   Z} _ = Nil
toVectFun {n = S m} f = (f FZ) :: (toVectFun (tail f))

N : Nat
N = 500

xs : Vect (S N) Nat
xs = toVectFun {n = S N} finToNat

main : IO ()
main = putStrLn $
  "xs(" ++ show N ++ ") = " ++ show (index (fromInteger (natToInteger N)) xs)
