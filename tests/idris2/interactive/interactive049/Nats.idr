module Nats

import Data.Nat

%default total

nats : (m : Nat) -> (n : Nat) -> (prf : NonZero n) -> m = n
