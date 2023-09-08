module AutoSearchHide1

public export
interface A where
  Value : Nat

public export
[ZeroA] A where
  Value = 0

public export
%hint
HintZeroA : A
HintZeroA = ZeroA

