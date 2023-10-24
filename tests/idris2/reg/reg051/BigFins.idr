module BigFins

import Control.Monad.State

import Data.Fin

%default total

public export
interface I a where
  fun : (a, a) -> a

export
{n : Nat} -> I (Fin $ S n) where
  fun = ?fin_rhs

export
printVerdict : HasIO m => a -> m ()
printVerdict it = ?printVerdict_rhs

N : Nat
N = 100000

St, D : Fin $ S N
St = 2000
D = 2004

main : IO ()
main = printVerdict $ fun {a=Fin $ S N} (St, St + D)
