module Issue833

import Data.Fin

%default total

data Singleton : Nat -> Type where
  Sing : {n : Nat} -> Singleton n

f : (n : Singleton Z) -> n === Sing
f = \ Sing => Refl

g : (k : Fin 1) -> k === FZ
g = \ FZ => Refl

sym : {t, u : a} -> t === u -> u === t
sym = \Refl => Refl
