module System.Random

import Data.Fin
import Data.Vect
import Data.List

public export
interface Random a where
  randomIO : HasIO io => io a

  ||| Takes a range (lo, hi), and returns a random value uniformly
  ||| distributed in the closed interval [lo, hi]. It is unspecified what
  ||| happens if lo > hi.
  randomRIO : HasIO io => (a, a) -> io a

%foreign "scheme:blodwen-random"
         "javascript:lambda:(max)=>Math.floor(Math.random() * max)"
prim__randomBits32 : Bits32 -> PrimIO Bits32

randomBits32 : Bits32 -> IO Bits32
randomBits32 upperBound = fromPrim (prim__randomBits32 upperBound)

public export
Random Int32 where
  -- Generate a random value within [-2^31, 2^31-1].
  randomIO = do
    let maxInt : Bits32    = 2147483647 -- shiftL 1 31 - 1
        negMinInt : Bits32 = 2147483648 -- negate $ shiftL 1 31
        magnitude : Bits32 = maxInt + negMinInt
    bits32 <- liftIO $ randomBits32 magnitude
    let int : Integer = cast bits32
    pure . cast $ int - (cast negMinInt)

  -- Generate a random value within [lo, hi].
  randomRIO (lo, hi) =
    let range : Integer = (cast hi) - (cast lo) + 1
     in pure . cast $ !(liftIO . randomBits32 $ cast range) + cast lo

%foreign "scheme:blodwen-random"
         "javascript:lambda:()=>Math.random()"
prim__randomDouble : PrimIO Double

randomDouble : IO Double
randomDouble = fromPrim prim__randomDouble

public export
Random Double where
  -- Generate a random value within [0, 1].
  randomIO = liftIO randomDouble

  -- Generate a random value within [lo, hi].
  randomRIO (lo, hi) = map ((+ lo) . (* (hi - lo))) (liftIO randomDouble)

%foreign "scheme:blodwen-random-seed"
prim__srand : Bits64 -> PrimIO ()

||| Sets the random seed
export
srand : Bits64 -> IO ()
srand n = fromPrim (prim__srand n)

||| Generate a random number in Fin (S `k`)
|||
||| Note that rndFin k takes values 0, 1, ..., k.
public export
rndFin : HasIO io => (n : Nat) -> io (Fin (S n))
rndFin 0 = pure FZ
rndFin (S k) = do
  let intBound = the Int32 (cast (S k))
  randomInt <- randomRIO (0, intBound)
  pure $ restrict (S k) (cast randomInt)

||| Select a random element from a vector
public export
rndSelect' : HasIO io => {k : Nat} -> Vect (S k) a -> io a
rndSelect' xs = pure $ Vect.index !(rndFin k) xs

||| Select a random element from a non-empty list
public export
rndSelect : HasIO io => (elems : List a) -> (0 _ : NonEmpty elems) => io a
rndSelect (x :: xs) = rndSelect' $ fromList (x :: xs)

