||| Additional properties/lemmata of Nats
module Data.Nat.Properties

import Data.Nat
import Syntax.PreorderReasoning

%default total

export
unfoldDouble : {0 n : Nat} -> (2 * n) === (n + n)
unfoldDouble = irrelevantEq $ cong (n +) (plusZeroRightNeutral _)

export
unfoldDoubleS : {0 n : Nat} -> (2 * S n) === (2 + 2 * n)
unfoldDoubleS = irrelevantEq $ Calc $
  |~ 2 * S n
  ~~ S n + S n   ...( unfoldDouble {n = S n} )
  ~~ 2 + (n + n) ...( sym (plusSuccRightSucc (S n) n) )
  ~~ 2 + 2 * n   ...( cong (2 +) (sym unfoldDouble) )

export
multRightCancel : (a,b,r : Nat) -> (0 _ : NonZero r) -> a*r = b*r -> a = b
multRightCancel a      b    0           r_nz ar_eq_br = void (absurd r_nz)
multRightCancel 0      0    r@(S predr) r_nz ar_eq_br = Refl
multRightCancel 0     (S b) r@(S predr) r_nz ar_eq_br impossible
multRightCancel (S a)  0    r@(S predr) r_nz ar_eq_br impossible
multRightCancel (S a) (S b) r@(S predr) r_nz ar_eq_br =
  cong S $ multRightCancel a b r r_nz
         $ plusLeftCancel r (a*r) (b*r) ar_eq_br
