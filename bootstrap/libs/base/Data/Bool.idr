module Data.Bool

%default total

export
notInvolutive : (x : Bool) -> not (not x) = x
notInvolutive True  = Refl
notInvolutive False = Refl

-- AND

export
andSameNeutral : (x : Bool) -> x && x = x
andSameNeutral False = Refl
andSameNeutral True = Refl

export
andFalseFalse : (x : Bool) -> x && False = False
andFalseFalse False = Refl
andFalseFalse True = Refl

export
andTrueNeutral : (x : Bool) -> x && True = x
andTrueNeutral False = Refl
andTrueNeutral True = Refl

export
andAssociative : (x, y, z : Bool) -> x && (y && z) = (x && y) && z
andAssociative True  _ _ = Refl
andAssociative False _ _ = Refl

export
andCommutative : (x, y : Bool) -> x && y = y && x
andCommutative x True  = andTrueNeutral x
andCommutative x False = andFalseFalse x

export
andNotFalse : (x : Bool) -> x && not x = False
andNotFalse False = Refl
andNotFalse True = Refl

-- OR

export
orSameNeutral : (x : Bool) -> x || x = x
orSameNeutral False = Refl
orSameNeutral True = Refl

export
orFalseNeutral : (x : Bool) -> x || False = x
orFalseNeutral False = Refl
orFalseNeutral True = Refl

export
orTrueTrue : (x : Bool) -> x || True = True
orTrueTrue False = Refl
orTrueTrue True = Refl

export
orAssociative : (x, y, z : Bool) -> x || (y || z) = (x || y) || z
orAssociative True  _ _ = Refl
orAssociative False _ _ = Refl

export
orCommutative : (x, y : Bool) -> x || y = y || x
orCommutative x True  = orTrueTrue x
orCommutative x False = orFalseNeutral x

export
orNotTrue : (x : Bool) -> x || not x = True
orNotTrue False = Refl
orNotTrue True = Refl

-- interaction & De Morgan's laws

export
orSameAndRightNeutral : (x, y : Bool) -> x || (x && y) = x
orSameAndRightNeutral False _ = Refl
orSameAndRightNeutral True  _ = Refl

export
andDistribOrR : (x, y, z : Bool) -> x && (y || z) = (x && y) || (x && z)
andDistribOrR False _ _ = Refl
andDistribOrR True  _ _ = Refl

export
orDistribAndR : (x, y, z : Bool) -> x || (y && z) = (x || y) && (x || z)
orDistribAndR False _ _ = Refl
orDistribAndR True  _ _ = Refl

export
notAndIsOr : (x, y : Bool) -> not (x && y) = not x || not y
notAndIsOr False _ = Refl
notAndIsOr True  _ = Refl

export
notOrIsAnd : (x, y : Bool) -> not (x || y) = not x && not y
notOrIsAnd False _ = Refl
notOrIsAnd True  _ = Refl

-- Interaction with typelevel `Not`

export
notTrueIsFalse : {1 x : Bool} -> Not (x = True) -> x = False
notTrueIsFalse {x=False} _ = Refl
notTrueIsFalse {x=True}  f = absurd $ f Refl

export
notFalseIsTrue : {1 x : Bool} -> Not (x = False) -> x = True
notFalseIsTrue {x=True} _  = Refl
notFalseIsTrue {x=False} f = absurd $ f Refl

--------------------------------------------------------------------------------
-- Decidability specialized on bool
--------------------------------------------------------------------------------

||| You can reverse decidability when bool is involved.
-- Given a contra on bool equality (a = b) -> Void, produce a proof of the opposite (that (not a) = b)
public export
invertContraBool : (a : Bool) -> (b : Bool) -> (a = b -> Void) -> (not a = b)
invertContraBool False False contra = absurd $ contra Refl
invertContraBool False True contra = Refl
invertContraBool True False contra = Refl
invertContraBool True True contra = absurd $ contra Refl
