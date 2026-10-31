import Data.Fin

record DefaultCode (code : a -> Type) where
  constructor MkDefault
  choose : {0 ty : a} -> code ty

Ex1,Ex2 : DefaultCode (Fin . S)

Ex1 = MkDefault (\{n} => FZ)
Ex2 = MkDefault {choose = \{n} => FZ}

Code : Nat -> Type
Code 0 = Fin 1
Code n = Fin n

aux : Nat -> Nat
aux 0 = 0
aux n@(S k) = k

Ex0' : DefaultCode Code
Ex0' = MkDefault $ \{n} =>
  replace {p = id} (case n of
    0 => Refl
    (S k) => Refl
  ) (Fin.FZ {k = aux n})

