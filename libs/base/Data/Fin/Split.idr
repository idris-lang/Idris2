||| Splitting operations and their properties
module Data.Fin.Split

import public Data.Fin
import Data.Fin.Properties

import Syntax.WithProof
import Syntax.PreorderReasoning

%default total

||| Converts `Fin`s that are used as indexes of parts to an index of a sum.
|||
||| For example, if you have a `Vect` that is a concatenation of two `Vect`s and
||| you have an index either in the first or the second of the original `Vect`s,
||| using this function you can get an index in the concatenated one.
public export
indexSum : {m : Nat} -> Either (Fin m) (Fin n) -> Fin (m + n)
indexSum (Left  l) = weakenN n l
indexSum (Right r) = shift m r

||| Extracts an index of the first or the second part from the index of a sum.
|||
||| For example, if you have a `Vect` that is a concatenation of the `Vect`s and
||| you have an index of this `Vect`, you have get an index of either left or right
||| original `Vect` using this function.
public export
splitSum : {m : Nat} -> Fin (m + n) -> Either (Fin m) (Fin n)
splitSum {m=Z}   k      = Right k
splitSum {m=S m} FZ     = Left FZ
splitSum {m=S m} (FS k) = mapFst FS $ splitSum k

||| Calculates the index of a square matrix of size `a * b` by indices of each side.
public export
indexProd : {n : Nat} -> Fin m -> Fin n -> Fin (m * n)
indexProd FZ     = weakenN $ mult (pred m) n
indexProd (FS k) = shift n . indexProd k

||| Splits the index of a square matrix of size `a * b` to indices of each side.
public export
splitProd : {m, n : Nat} -> Fin (m * n) -> (Fin m, Fin n)
splitProd {m=S _} p = case splitSum p of
  Left  k => (FZ, k)
  Right l => mapFst FS $ splitProd l

--- Properties ---

export
indexSumPreservesLast :
  (m, n : Nat) -> indexSum {m} (Right $ Fin.last {n}) ~~~ Fin.last {n=m+n}
indexSumPreservesLast Z     n = reflexive
indexSumPreservesLast (S m) n = FS (shiftLastIsLast m)

export
indexProdPreservesLast : (m, n : Nat) ->
         indexProd (Fin.last {n=m}) (Fin.last {n}) = Fin.last
indexProdPreservesLast Z n = homoPointwiseIsEqual
  $ transitive (weakenNZeroIdentity last)
               (congLast (sym $ plusZeroRightNeutral n))
indexProdPreservesLast (S m) n = Calc $
  |~ indexProd (last {n=S m}) (last {n})
  ~~ FS (shift n (indexProd last last)) ...( Refl )
  ~~ FS (shift n last)                  ...( cong (FS . shift n) (indexProdPreservesLast m n ) )
  ~~ last                               ...( homoPointwiseIsEqual prf )

  where

    prf : shift (S n) (Fin.last {n = n + m * S n}) ~~~ Fin.last {n = n + S (n + m * S n)}
    prf = transitive (shiftLastIsLast (S n))
                     (congLast (plusSuccRightSucc n (n + m * S n)))

export
splitSumOfWeakenN : (k : Fin m) -> splitSum {m} {n} (weakenN n k) = Left k
splitSumOfWeakenN FZ = Refl
splitSumOfWeakenN (FS k) = cong (mapFst FS) $ splitSumOfWeakenN k

export
splitSumOfShift : {m : Nat} -> (k : Fin n) -> splitSum {m} {n} (shift m k) = Right k
splitSumOfShift {m=Z}   k = Refl
splitSumOfShift {m=S m} k = cong (mapFst FS) $ splitSumOfShift k

export
splitOfIndexSumInverse : {m : Nat} -> (e : Either (Fin m) (Fin n)) -> splitSum (indexSum e) = e
splitOfIndexSumInverse (Left l) = splitSumOfWeakenN l
splitOfIndexSumInverse (Right r) = splitSumOfShift r

export
indexOfSplitSumInverse : {m, n : Nat} -> (f : Fin (m + n)) -> indexSum (splitSum {m} {n} f) = f
indexOfSplitSumInverse {m=Z}   f  = Refl
indexOfSplitSumInverse {m=S _} FZ = Refl
indexOfSplitSumInverse {m=S _} (FS f) with (indexOfSplitSumInverse f)
  indexOfSplitSumInverse {m=S _} (FS f) | eq with (splitSum f)
    indexOfSplitSumInverse {m=S _} (FS _) | eq | Left  _ = cong FS eq
    indexOfSplitSumInverse {m=S _} (FS _) | eq | Right _ = cong FS eq


export
splitOfIndexProdInverse : {m : Nat} -> (k : Fin m) -> (l : Fin n) ->
                          splitProd (indexProd k l) = (k, l)
splitOfIndexProdInverse FZ     l
   = rewrite splitSumOfWeakenN {n = mult (pred m) n} l in Refl
splitOfIndexProdInverse (FS k) l
   = rewrite splitSumOfShift {m=n} $ indexProd k l in
     cong (mapFst FS) $ splitOfIndexProdInverse k l

export
indexOfSplitProdInverse : {m, n : Nat} -> (f : Fin (m * n)) ->
                          uncurry (indexProd {m} {n}) (splitProd {m} {n} f) = f
indexOfSplitProdInverse {m = S _} f with (@@ splitSum f)
  indexOfSplitProdInverse {m = S _} f | (Left l ** eq) = rewrite eq in Calc $
    |~ indexSum (Left l)
    ~~ indexSum (splitSum f) ...( cong indexSum (sym eq) )
    ~~ f                     ...( indexOfSplitSumInverse f )
  indexOfSplitProdInverse f | (Right r ** eq) with (@@ splitProd r)
    indexOfSplitProdInverse f | (Right r ** eq) | ((p, q) ** eq2)
      = rewrite eq in rewrite eq2 in Calc $
        |~ indexProd (FS p) q
        ~~ shift n (indexProd p q)                   ...( Refl )
        ~~ shift n (uncurry indexProd (splitProd r)) ...( cong (shift n . uncurry indexProd) (sym eq2) )
        ~~ shift n r                                 ...( cong (shift n) (indexOfSplitProdInverse r) )
        ~~ indexSum (splitSum f)                     ...( sym (cong indexSum eq) )
        ~~ f                                         ...( indexOfSplitSumInverse f )
