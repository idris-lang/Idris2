namespace AAA
  public export
  unit_no_body : Unit
  public export
  unit_filled : Unit
  unit_filled = MkUnit

data View : Unit -> Type where
  V_unit_filled : View AAA.unit_filled
  V_unit_no_body : View AAA.unit_no_body

delete : (v : Unit) -> View v -> Unit
delete _ V_unit_filled = MkUnit
delete _ V_unit_no_body = MkUnit

aaa : Equal (delete AAA.unit_no_body V_unit_no_body) MkUnit
aaa = Refl
