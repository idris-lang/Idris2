module Data.Bool.Extra

public export
andSameNeutral : (x : Bool) -> x && x = x
andSameNeutral False = Refl
andSameNeutral True = Refl

public export
andFalseFalse : (x : Bool) -> x && False = False
andFalseFalse False = Refl
andFalseFalse True = Refl

public export
andTrueNeutral : (x : Bool) -> x && True = x
andTrueNeutral False = Refl
andTrueNeutral True = Refl

public export
orSameNeutral : (x : Bool) -> x || x = x
orSameNeutral False = Refl
orSameNeutral True = Refl

public export
orFalseNeutral : (x : Bool) -> x || False = x
orFalseNeutral False = Refl
orFalseNeutral True = Refl

public export
orTrueTrue : (x : Bool) -> x || True = True
orTrueTrue False = Refl
orTrueTrue True = Refl

public export
orSameAndRightNeutral : (x, right : Bool) -> x || (x && right) = x
orSameAndRightNeutral False _ = Refl
orSameAndRightNeutral True _ = Refl
