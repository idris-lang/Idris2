%unbound_implicits off

record JamesBondTheme where
  isVinyl : Bool

-- The James Bond Equality states that for every record field `f`,
-- the prefix form `f` must be definitionally equal to `.f`.
jbeq : isVinyl = (.isVinyl)
jbeq = Refl

-- Then its applications are seamlessly interchangeable, too.
jbeqApp : (rec : JamesBondTheme) -> isVinyl rec = rec.isVinyl
jbeqApp _ = Refl
