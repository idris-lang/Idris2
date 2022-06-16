import Language.Reflection

import Data.Vect

%language ElabReflection

%macro
coolMacro : Nat -> Elab (Nat -> Nat)
coolMacro n = lambda Nat $ \m => pure $ n + m + 1

Cool_indirect : Nat
Cool_indirect = let z = coolMacro 4 in z 5

Cool_direct : Nat
Cool_direct = coolMacro 4 5

cool_eq : Cool_indirect = Cool_direct
cool_eq = Refl

cool_eq' : Cool_indirect ~=~ coolMacro 4 5
cool_eq' = Refl

Cool_direct' : ?
Cool_direct' = coolMacro 4 5

cool_eq'' : Cool_indirect ~=~ Cool_direct'
cool_eq'' = Refl

%macro
depMacro : (b : Bool) -> if b then Elab (Nat -> Nat) else Nat -> Elab Nat
depMacro False = \m => pure $ m + 100
depMacro True  = lambda Nat $ \m => pure $ m + 200

Dep_indirect_t : Nat
Dep_indirect_t = let z = depMacro True in z 5

Dep_direct_t : Nat
Dep_direct_t = depMacro True 5

dep_t : Dep_indirect_t = Dep_direct_t
dep_t = Refl

dep_t' : Dep_indirect_t ~=~ depMacro True 5
dep_t' = Refl

dep_t'' : S Dep_indirect_t ~=~ S (depMacro True 5)
dep_t'' = Refl

Dep_indirect_f : Nat
Dep_indirect_f = let z = depMacro False 5 in z

Dep_direct_f : Nat
Dep_direct_f = depMacro False 5

dep_f : Dep_indirect_f = Dep_direct_f
dep_f = Refl

dep_f' : Dep_indirect_f ~=~ depMacro False 5
dep_f' = Refl

dep_f'' : S Dep_indirect_f ~=~ S (depMacro False 5)
dep_f'' = Refl

%macro
depDepMacro : (b : Bool) -> if b then Elab ((n : Nat) -> Vect n Nat) else (n : Nat) -> Elab $ Vect n Nat
depDepMacro False = \m => pure $ replicate m 0
depDepMacro True  = lambda Nat $ \m => pure $ replicate m 1

DepDep_indirect_t : Vect ? Nat
DepDep_indirect_t = let z = depDepMacro True in z 5

DepDep_direct_t : Vect ? Nat
DepDep_direct_t = depDepMacro True 5

depDep_t : DepDep_indirect_t = DepDep_direct_t
depDep_t = Refl

depDep_t' : DepDep_indirect_t = depDepMacro True 5
depDep_t' = Refl

depDep_t'' : 9 :: DepDep_indirect_t = 9 :: depDepMacro True 5
depDep_t'' = Refl

DepDep_indirect_f : Vect ? Nat
DepDep_indirect_f = let z = depDepMacro False 5 in z

DepDep_direct_f : Vect ? Nat
DepDep_direct_f = depDepMacro False 5

depDep_f : DepDep_indirect_f = DepDep_direct_f
depDep_f = Refl

depDep_f' : DepDep_indirect_f = depDepMacro False 5
depDep_f' = Refl

depDep_f'' : 9 :: DepDep_indirect_f = 9 :: depDepMacro False 5
depDep_f'' = Refl
