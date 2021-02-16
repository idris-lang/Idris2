module Decidable.Equality.Core

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
negEqSym : forall a, b . (a = b -> Void) -> (b = a -> Void)
negEqSym p h = p (sym h)

||| Everything is decidably equal to itself
export
decEqSelfIsYes : DecEq a => {x : a} -> decEq x x = Yes Refl
decEqSelfIsYes {x} with (decEq x x)
  decEqSelfIsYes {x} | Yes Refl = Refl
  decEqSelfIsYes {x} | No contra = absurd $ contra Refl

||| If you have a proof of inequality, you're sure that `decEq` would give a `No`.
export
decEqContraIsNo : DecEq a => {x, y : a} -> Not (x = y) -> (p ** decEq x y = No p)
decEqContraIsNo uxy with (decEq x y)
  decEqContraIsNo uxy | Yes xy = absurd $ uxy xy
  decEqContraIsNo _   | No uxy = (uxy ** Refl)
