module Algebra.ZeroOneOmega

import Algebra.Semiring
import Algebra.Preorder

export
data ZeroOneOmega = Rig0 | Rig1 | RigW

Preorder ZeroOneOmega where
  Rig0 <= _ = True
  Rig1 <= Rig1 = True
  Rig1 <= RigW = True
  RigW <= RigW = True
  _ <= _ = False
  preorderRefl {x = Rig0} = Refl
  preorderRefl {x = Rig1} = Refl
  preorderRefl {x = RigW} = Refl
  preorderTrans {x = Rig0} {y = y} {z = z} a b = Refl
  preorderTrans {x = Rig1} {y = Rig0} {z = Rig0} Refl Refl impossible
  preorderTrans {x = Rig1} {y = Rig1} {z = Rig0} _ Refl impossible
  preorderTrans {x = Rig1} {y = RigW} {z = Rig0} _ Refl impossible
  preorderTrans {x = Rig1} {y = y} {z = Rig1} a b = Refl
  preorderTrans {x = Rig1} {y = y} {z = RigW} a b = Refl
  preorderTrans {x = RigW} {y = Rig0} {z = _} Refl _ impossible
  preorderTrans {x = RigW} {y = Rig1} {z = _} Refl _ impossible
  preorderTrans {x = RigW} {y = RigW} {z = z} a b = b

public export
Eq ZeroOneOmega where
  (==) Rig0 Rig0 = True
  (==) Rig1 Rig1 = True
  (==) RigW RigW = True
  (==) _ _ = False

export
Show ZeroOneOmega where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

export
rigPlus : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigPlus Rig0 a = a
rigPlus a Rig0 = a
rigPlus Rig1 a = RigW
rigPlus a Rig1 = RigW
rigPlus RigW RigW = RigW

export
rigMult : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigMult Rig0 _ = Rig0
rigMult _ Rig0 = Rig0
rigMult Rig1 a = a
rigMult a Rig1 = a
rigMult RigW RigW = RigW

public export
Semiring ZeroOneOmega where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = Rig0
  timesNeutral = Rig1

||| The top value of a lattice
export
Top ZeroOneOmega where
  top = RigW
  topAbs {x = Rig0} = Refl
  topAbs {x = Rig1} = Refl
  topAbs {x = RigW} = Refl
