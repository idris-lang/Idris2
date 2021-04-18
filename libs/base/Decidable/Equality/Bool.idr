module Decidable.Equality.Bool

%default total

--------------------------------------------------------------------------------
-- Decidability specialized on bool
--------------------------------------------------------------------------------

||| You can reverse decidability when bool is involved.
-- Given a contra on bool equality (a = b) -> Void, produce a proof of the opposite (that (not a) = b)
public export
invertContraBool : (a : Bool) -> (b : Bool) -> (a = b -> Void) -> (not a = b)
invertContraBool a b contra = invertContraBool_ a b contra
  where
    fEf : False = False
    fEf = Refl

    tEt : True = True
    tEt = Refl

    invertContraBool_ : (a : Bool) -> (b : Bool) -> (a = b -> Void) -> (not a = b)
    invertContraBool_ False False contra = absurd (contra fEf)
    invertContraBool_ False True contra = Refl
    invertContraBool_ True False contra = Refl
    invertContraBool_ True True contra = absurd (contra tEt)
