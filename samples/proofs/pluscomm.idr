plus_commutes_Z : (m : Nat) -> m = plus m Z
plus_commutes_Z Z = Refl
plus_commutes_Z (S k)
   = let rec = plus_commutes_Z k in
         rewrite sym rec in Refl

plus_commutes_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_S k Z = Refl
plus_commutes_S k (S j)
   = rewrite plus_commutes_S k j in Refl

total
plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z m = plus_commutes_Z m
plus_commutes (S k) m
    = rewrite plus_commutes k m in
              plus_commutes_S k m
