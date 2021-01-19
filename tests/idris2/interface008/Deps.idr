data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)

interface Finite t where
  0 card   : Nat
  to     : t -> Fin card

implementation Finite (Fin k) where
  card = k
  to = id

interface BadFinite t where
  badcard   : Nat
  badto     : t -> Fin card

implementation BadFinite (Fin k) where
  badcard = k
  badto = id
