data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)

interface Finite t where
  card   : Nat
  to     : t -> Fin card
  from   : Fin card -> t
  toFrom : (k : Fin card) -> to (from k) = k
  fromTo : (x : t) -> from (to x) = x

-- Checking dependent methods work, and that having names from the
-- methods shadowed in the interface head doesn't cause any issues

implementation Finite (Fin k) where
  card   = ?ncard
  to     = ?lala
  from   = ?lula
  toFrom = ?foo
  fromTo = ?bar

implementation Finite (Fin n) where
  card   = ?ncard1
  to     = ?lala1
  from   = ?lula1
  toFrom = ?foo1
  fromTo = ?bar1

implementation Finite (Fin t) where
  card   = ?ncard2
  to     = ?lala2
  from   = ?lula2
  toFrom = ?foo2
  fromTo = ?bar2
