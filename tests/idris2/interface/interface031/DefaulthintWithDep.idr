interface X where
  x : Nat

f : X => Nat
f = x + 1

namespace NoHintArg

  %defaulthint
  DefaultX : X
  DefaultX = D where
    [D] X where x = 5

  fDef : Nat
  fDef = f

namespace WithDefaultHintArg

  interface Y' where
    y : Nat

  [YY] Y' where
    y = 6

  %defaulthint
  YY' : Y'
  YY' = YY

  %defaulthint
  DefaultX : Y' => X
  DefaultX = D where
    [D] X where x = 5

  fDef : Nat
  fDef = f

namespace JustHint

  interface Y'' where
    y : Nat

  Y'' where
    y = 6

  %hint
  DefaultX : Y'' => X
  DefaultX = D where
    [D] X where x = 5

  fDef : Nat
  fDef = f

namespace WithHintArg

  interface Y''' where
    y : Nat

  Y''' where
    y = 6

  %defaulthint
  DefaultX : Y''' => X
  DefaultX = D where
    [D] X where x = 5

  fDef : Nat
  fDef = f
