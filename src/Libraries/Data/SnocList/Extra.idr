module Libraries.Data.SnocList.Extra

import Data.SnocList

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
