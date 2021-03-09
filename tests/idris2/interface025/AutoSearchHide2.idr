module AutoSearchHide2

import AutoSearchHide1

myZero : Value === 0
myZero = Refl

[OneA] A where
  Value = 1

%hint
HintOneA : A
HintOneA = OneA

-- Want to use the OneA (via HintOneA) instance here.

-- `%hide` should block the auto-search from
-- including the `HintZeroA` hint into the list of solutions.
-- Thus, we don't get into the `multiple solutions` situation.
%hide HintZeroA
myOne : Value === 1
myOne = Refl
