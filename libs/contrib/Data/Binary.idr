module Data.Binary

import Data.Nat.Properties
import Data.Binary.Digit
import Syntax.PreorderReasoning

%default total

||| Bin represents binary numbers right-to-left.
||| For instance `4` can be represented as `OOI`.
||| Note that representations are not unique: one may append arbitrarily
||| many Os to the right of the representation without changing the meaning.
public export
Bin : Type
Bin = List Digit

||| Conversion from lists of bits to natural number.
public export
toNat : Bin -> Nat
toNat = foldr (\ b, acc => toNat b + 2 * acc) 0

||| Successor function on binary numbers.
||| Amortised constant time.
public export
suc : Bin -> Bin
suc [] = [I]
suc (O :: bs) = I :: bs
suc (I :: bs) = O :: (suc bs)

||| Correctness proof of `suc` with respect to the semantics in terms of Nat
export
sucCorrect : {bs : Bin} -> toNat (suc bs) === S (toNat bs)
sucCorrect {bs = []} = Refl
sucCorrect {bs = O :: bs} = Refl
sucCorrect {bs = I :: bs} = Calc $
  |~ toNat (suc (I :: bs))
  ~~ toNat (O :: suc bs) ...( Refl )
  ~~ 2 * toNat (suc bs)  ...( Refl )
  ~~ 2 * S (toNat bs)    ...( cong (2 *) sucCorrect )
  ~~ 2 + 2 * toNat bs    ...( unfoldDoubleS )
  ~~ S (toNat (I :: bs)) ...( Refl )
