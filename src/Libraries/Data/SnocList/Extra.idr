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
lengthDistributesOverFish : (sx : SnocList a) -> (ys : List a) ->
                            length (sx <>< ys) === length sx + length ys
lengthDistributesOverFish sx [] = sym $ plusZeroRightNeutral _
lengthDistributesOverFish sx (y :: ys) = Calc $
  |~ length ((sx :< y) <>< ys)
  ~~ length (sx :< y) + length ys ...( lengthDistributesOverFish (sx :< y) ys )
  ~~ S (length sx) + length ys    ...( Refl )
  ~~ length sx + S (length ys)    ...( plusSuccRightSucc _ _ )
  ~~ length sx + length (y :: ys) ...( Refl )

||| Insert some separator between the elements of a snoc-list.
|||
||| @ sep the value to intersperse
||| @ xs  the snoc-list of elements to intersperse with the separator
|||
||| ```idris example
||| > with SnocList (intersperse ',' [<'a', 'b', 'c', 'd', 'e'])
||| [<'a', ',', 'b', ',', 'c', ',', 'd', ',', 'e']
||| ```
public export
intersperse : (sep : a) -> (xs : SnocList a) -> SnocList a
intersperse sep [<]     = [<]
intersperse sep [<x]    = [<x]
intersperse sep (xs:<x) = intersperse sep xs :< sep :< x

||| Joins the strings using the provided separator
||| ```idris example
||| joinBy ", " [<"A", "BC", "D"] === "A, BC, D"
||| ```
public export
joinBy : String -> SnocList String -> String
joinBy sep ws = concat (intersperse sep ws)
