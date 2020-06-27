data BNat = BZ | O BNat | E BNat

bnat_ind : {0 p : BNat -> Type}
        -> p BZ
        -> ((bn : BNat) -> p bn -> p (O bn))
        -> ((bn : BNat) -> p bn -> p (E bn))
        -> (bn : BNat) -> p bn
bnat_ind pbz po pe = go
 where
  go : (bn : BNat) -> p bn
  go BZ = ?pbz_hole
  go (O x) = po x (go x)
  go (E x) = pe x (go x)
