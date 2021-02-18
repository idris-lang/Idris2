module Data.Nat.Views

import Control.WellFounded
import Data.Nat

%default total

||| View for dividing a Nat in half
public export
data Half : Nat -> Type where
     HalfOdd : (n : Nat) -> Half (S (n + n))
     HalfEven : (n : Nat) -> Half (n + n)

||| View for dividing a Nat in half, recursively
public export
data HalfRec : Nat -> Type where
     HalfRecZ : HalfRec Z
     HalfRecEven : (n : Nat) -> (rec : Lazy (HalfRec n)) -> HalfRec (n + n)
     HalfRecOdd : (n : Nat) -> (rec : Lazy (HalfRec n)) -> HalfRec (S (n + n))

||| Covering function for the `Half` view
public export
half : (n : Nat) -> Half n
half Z = HalfEven Z
half (S k) with (half k)
  half (S (S (n + n))) | HalfOdd n = rewrite plusSuccRightSucc (S n) n in
                                           HalfEven (S n)
  half (S (n + n)) | HalfEven n = HalfOdd n

public export
halfRec : (n : Nat) -> HalfRec n
halfRec n with (sizeAccessible n)
  halfRec  Z | acc = HalfRecZ
  halfRec (S n) | acc with (half n)
    halfRec (S (S (k + k))) | Access acc | HalfOdd k
      = rewrite plusSuccRightSucc (S k) k
          in HalfRecEven _ (halfRec (S k) | acc (S k) (LTESucc (LTESucc (lteAddRight _))))
    halfRec (S (k + k)) | Access acc | HalfEven k
      = HalfRecOdd _ (halfRec k | acc k (LTESucc (lteAddRight _)))

public export
||| Raises a number to a power which is a natural number.
(^) : Num ty => ty -> Nat -> ty
(^) x k = fastPow k x 1 where
  ||| Raises a number to a natural-number-power using repeated squaring.
  fastPow : Nat -> ty -> ty -> ty
  fastPow k x res with (halfRec k)
    fastPow Z x res | HalfRecZ = res
    fastPow (m + m) x res | (HalfRecEven m rec) = fastPow m (x * x) res | rec
    fastPow (S (m + m)) x res | (HalfRecOdd m rec) = fastPow m (x * x) (res * x) | rec
