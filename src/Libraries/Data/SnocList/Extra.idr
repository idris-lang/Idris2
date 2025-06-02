module Libraries.Data.SnocList.Extra

import Data.Nat
import Data.SnocList
import Syntax.PreorderReasoning

-- TODO left-to-right reversal of the stream
--      is this what we want?
public export
take : (n : Nat) -> (xs : Stream a) -> SnocList a
take Z xs = [<]
take (S k) (x :: xs) = take k xs :< x

public export
snocAppendFishAssociative :
  (sx, sy : SnocList a) -> (zs : List a) ->
  (sx ++ sy) <>< zs === sx ++ (sy <>< zs)
snocAppendFishAssociative sx sy [] = Refl
snocAppendFishAssociative sx sy (z :: zs)
  = snocAppendFishAssociative sx (sy :< z) zs

export
snocAppendAsFish : (sx, sy : SnocList a) -> sx ++ sy === sx <>< (cast sy)
snocAppendAsFish sx sy = sym
  $ trans (fishAsSnocAppend sx (sy <>> []))
          (cong (sx ++) (castToList sy))

export
revOnto : (xs, vs : SnocList a) -> reverseOnto xs vs = xs ++ reverse vs
revOnto xs [<] = Refl
revOnto xs (vs :< v)
    = rewrite Extra.revOnto (xs :< v) vs in
        rewrite Extra.revOnto [<v] vs in
          rewrite appendAssociative xs [<v] (reverse vs) in Refl

export
lookup : Eq a => a -> SnocList (a, b) -> Maybe b
lookup n [<] = Nothing
lookup n (ns :< (x, n')) = if x == n then Just n' else lookup n ns

lengthDistributesOverAppend
  : (xs, ys : SnocList a)
  -> length (ys ++ xs) = length xs + length ys
lengthDistributesOverAppend [<] ys = Refl
lengthDistributesOverAppend (xs :< x) ys =
  cong S $ lengthDistributesOverAppend xs ys

export
lengthDistributesOverFish : (sx : SnocList a) -> (ys : List a) ->
                            length (sx <>< ys) === length sx + length ys
lengthDistributesOverFish sx [] = sym $ plusZeroRightNeutral _
lengthDistributesOverFish sx (y :: ys) = Calc $
  |~ length ((sx :< y) <>< ys)
  ~~ length (sx :< y) + length ys ...( lengthDistributesOverFish (sx :< y) ys )
  ~~ S (length sx) + length ys    ...( Refl )
  ~~ length sx + S (length ys)    ...( plusSuccRightSucc _ _ )
  ~~ length sx + length (y :: ys) ...( Refl )
