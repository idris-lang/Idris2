import Data.Nat

lteZeroSuccAbsurd : LTE (S Z) Z -> Void
lteZeroSuccAbsurd y = absurd y

lteSuccAbsurd : LTE (S x) x -> Void
lteSuccAbsurd y = succNotLTEpred y

