data BNat = BZ | O BNat | E BNat

data BLT : BNat -> BNat -> Type where
  BLT_ZO : BLT BZ (O bn)
  BLT_ZE : BLT BZ (E bn)
  BLT_OO : BLT bn bm -> BLT (O bn) (O bm)
  BLT_OE : BLT bn bm -> BLT (O bn) (E bm)
  BLT_OE_Eq : BLT (O bn) (E bn)
  BLT_EO : BLT bn bm -> BLT (E bn) (O bm)
  BLT_EE : BLT bn bm -> BLT (E bn) (E bm)

notLtz : BLT bn BZ -> Void
notLtz x = ?notLtz_rhs
