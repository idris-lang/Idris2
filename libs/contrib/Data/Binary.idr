module Data.Binary

import Data.Nat
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
Cast Bin Nat where
  cast = foldr (\ b, acc => cast b + 2 * acc) 0

||| Successor function on binary numbers.
||| Amortised constant time.
public export
suc : Bin -> Bin
suc [] = [I]
suc (O :: bs) = I :: bs
suc (I :: bs) = O :: (suc bs)

||| Correctness proof of `suc` with respect to the semantics in terms of Nat
export
sucCorrect : {bs : Bin} -> cast (suc bs) === S (cast bs)
sucCorrect {bs = []} = Refl
sucCorrect {bs = O :: bs} = Refl
sucCorrect {bs = I :: bs} = Calc $
  |~ cast (suc (I :: bs))
  ~~ cast (O :: suc bs) ...( Refl )
  ~~ 2 * cast (suc bs)  ...( Refl )
  ~~ 2 * S (cast bs)    ...( cong (2 *) sucCorrect )
  ~~ 2 + 2 * cast bs    ...( unfoldDoubleS )
  ~~ S (cast (I :: bs)) ...( Refl )
