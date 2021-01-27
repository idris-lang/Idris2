data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just FZ
natToFin (S k) (S j)
   = case natToFin k j of
          Just k' => Just (FS k')
          Nothing => Nothing
natToFin _ _ = Nothing

integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x Z = Nothing
integerToFin x n = if x >= 0 then natToFin (fromInteger x) n else Nothing

data IsJust : Maybe a -> Type where
     ItIsJust : IsJust (Just x)

-- Testing that %allow_overloads lets this one through!
partial
fromInteger : {k : Nat} ->
              (n : Integer) ->
              {auto prf : IsJust (integerToFin n k)} ->
              Fin k
fromInteger {k} n {prf}
    = case integerToFin n k of
           Just val => val

foo : Fin 5
foo = 3

bar : Fin 5
bar = 8
