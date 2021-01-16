||| Additional properties/lemmata of Nats
module Data.Nat.Properties

import Data.Nat

%default total

export
multRightCancel : (a,b,r : Nat) -> Not (r = 0) -> a*r = b*r -> a = b
multRightCancel a      b    0           r_nz ar_eq_br = void $ r_nz Refl
multRightCancel 0      0    r@(S predr) r_nz ar_eq_br = Refl
multRightCancel 0     (S b) r@(S predr) r_nz ar_eq_br impossible
multRightCancel (S a)  0    r@(S predr) r_nz ar_eq_br impossible
multRightCancel (S a) (S b) r@(S predr) r_nz ar_eq_br =
  cong S $ multRightCancel a b r r_nz
         $ plusLeftCancel r (a*r) (b*r) ar_eq_br

