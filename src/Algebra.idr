module Algebra

import public Algebra.ZeroOneOmega
import public Algebra.Semiring
import public Algebra.Preorder

%default total

public export
RigCount : Type
RigCount = ZeroOneOmega

export
showCount : RigCount -> String
showCount = elimSemi "0 " "1 " (const "")
