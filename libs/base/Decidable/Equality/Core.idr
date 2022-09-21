module Decidable.Equality.Core

import Control.Function

%default total

--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

||| Decision procedures for propositional equality
public export
interface DecEq t where
  ||| Decide whether two elements of `t` are propositionally equal
  decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

||| The negation of equality is symmetric (follows from symmetry of equality)
export
negEqSym : Not (a = b) -> Not (b = a)
negEqSym p h = p (sym h)

||| Everything is decidably equal to itself
export
decEqSelfIsYes : DecEq a => {x : a} -> decEq x x = Yes Refl
decEqSelfIsYes with (decEq x x)
  decEqSelfIsYes | Yes Refl = Refl
  decEqSelfIsYes | No contra = absurd $ contra Refl

||| If you have a proof of inequality, you're sure that `decEq` would give a `No`.
export
decEqContraIsNo : DecEq a => {x, y : a} -> Not (x = y) -> (p ** decEq x y = No p)
decEqContraIsNo uxy with (decEq x y)
  decEqContraIsNo uxy | Yes xy = absurd $ uxy xy
  decEqContraIsNo _   | No uxy = (uxy ** Refl)

public export
decEqCong : (0 _ : Injective f) => Dec (x = y) -> Dec (f x = f y)
decEqCong $ Yes prf   = Yes $ cong f prf
decEqCong $ No contra = No $ \c => contra $ inj f c

public export
decEqInj : (0 _ : Injective f) => Dec (f x = f y) -> Dec (x = y)
decEqInj $ Yes prf   = Yes $ inj f prf
decEqInj $ No contra = No $ contra . cong f

public export
decEqCong2 : (0 _ : Biinjective f) => Dec (x = y) -> Lazy (Dec (v = w)) -> Dec (f x v = f y w)
decEqCong2 (Yes Refl)  s = decEqCong s @{FromBiinjectiveL}
decEqCong2 (No contra) _ = No $ \c => let (Refl, Refl) = biinj f c in contra Refl
