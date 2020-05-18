module System.Random

import Data.Fin
import Data.Vect
import Data.List

public export
interface Random a where
  randomIO : IO a

  -- Takes a range (lo, hi), and returns a random value uniformly
  -- distributed in the closed interval [lo, hi]. It is unspecified what
  -- happens if lo > hi.
  randomRIO : (a, a) -> IO a

prim_randomInt : Int -> IO Int
prim_randomInt upperBound = schemeCall Int "blodwen-random" [upperBound]

public export
Random Int where
  -- Generate a random value within [-2^31, 2^31-1].
  randomIO =
    let maxInt = shiftL 1 31 - 1
        minInt = negate $ shiftL 1 31
        range = maxInt - minInt
     in map (+ minInt) $ prim_randomInt range

  -- Generate a random value within [lo, hi].
  randomRIO (lo, hi) =
    let range = hi - lo + 1
     in map (+ lo) $ prim_randomInt range

prim_randomDouble : IO Double
prim_randomDouble = schemeCall Double "blodwen-random" []

public export
Random Double where
  -- Generate a random value within [0, 1].
  randomIO = prim_randomDouble

  -- Generate a random value within [lo, hi].
  randomRIO (lo, hi) = map ((+ lo) . (* (hi - lo))) prim_randomDouble

||| Sets the random seed
export
srand : Integer -> IO ()
srand n = schemeCall () "blodwen-random-seed" [n]

||| Generate a random number in Fin (S `k`)
|||
||| Note that rndFin k takes values 0, 1, ..., k.
public export
rndFin : (n : Nat) -> IO (Fin (S n))
rndFin 0 = pure FZ
rndFin (S k) = do
  let intBound = the Int (cast (S k))
  randomInt <- randomRIO (0, intBound)
  pure $ restrict (S k) (cast randomInt)

||| Select a random element from a vector
public export
rndSelect' : {k : Nat} -> Vect (S k) a -> IO a
rndSelect' {k} xs = pure $ Vect.index !(rndFin k) xs

||| Select a random element from a non-empty list
public export
rndSelect : (elems : List a) -> {auto prf : NonEmpty elems} -> IO a
rndSelect (x :: xs) {prf = IsNonEmpty} = rndSelect' $ fromList (x :: xs)
