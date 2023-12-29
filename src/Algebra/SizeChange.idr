module Algebra.SizeChange

import Algebra.Semiring

import Libraries.Text.PrettyPrint.Prettyprinter

public export
data SizeChange = Smaller | Same | Unknown

export
Semigroup SizeChange where
  -- Same is a neutral
  Unknown <+> _ = Unknown
  Same <+> c = c
  _ <+> Unknown = Unknown
  Smaller <+> _ = Smaller

export
Monoid SizeChange where
  neutral = Same

export
Show SizeChange where
  show Smaller = "Smaller"
  show Same = "Same"
  show Unknown = "Unknown"

export
Eq SizeChange where
  Smaller == Smaller = True
  Same == Same = True
  Unknown == Unknown = True
  _ == _ = False

-- information order
export
Ord SizeChange where
  compare Unknown Unknown = EQ
  compare Unknown _ = LT
  compare _ Unknown = GT
  compare Same Same = EQ
  compare Same _ = LT
  compare _ Same = GT
  compare Smaller Smaller = EQ

  max Unknown y = y
  max Same Unknown = Same
  max Same y = y
  max Smaller y = Smaller -- holds definitionally!

export
Semiring SizeChange where
  (|*|) = (<+>)
  timesNeutral = neutral
  (|+|) = max
  plusNeutral = Unknown

-- semiring laws
scPlusNeutralLeft : (a : SizeChange) -> Unknown |+| a = a
scPlusNeutralLeft a = Refl

scPlusNeutralRight : (a : SizeChange) -> a |+| Unknown = a
scPlusNeutralRight Smaller = Refl
scPlusNeutralRight Same = Refl
scPlusNeutralRight Unknown = Refl

partial
scPlusCommutative : (a, b : SizeChange) -> a |+| b = b |+| a
scPlusCommutative Unknown b = sym (scPlusNeutralRight b)
scPlusCommutative b Unknown = scPlusNeutralRight b
scPlusCommutative Smaller Smaller = Refl
scPlusCommutative Same Smaller = Refl
scPlusCommutative Smaller Same = Refl
scPlusCommutative Same Same = Refl

scPlusAssoc : (a, b, c : SizeChange) -> (a |+| b) |+| c = a |+| (b |+| c)
scPlusAssoc Smaller b c = Refl
scPlusAssoc Same Smaller c = Refl
scPlusAssoc Same Same Smaller = Refl
scPlusAssoc Same Same Same = Refl
scPlusAssoc Same Same Unknown = Refl
scPlusAssoc Same Unknown c = Refl
scPlusAssoc Unknown b c = Refl

scMultNeutralLeft : (a : SizeChange) -> Same |*| a = a
scMultNeutralLeft a = Refl

scMultNeutralRight : (a : SizeChange) -> a |*| Same = a
scMultNeutralRight Smaller = Refl
scMultNeutralRight Same = Refl
scMultNeutralRight Unknown = Refl

scMultZeroLeft : (a : SizeChange) -> Unknown |*| a = Unknown
scMultZeroLeft a = Refl

scMultZeroRight : (a : SizeChange) -> a |*| Unknown = Unknown
scMultZeroRight Smaller = Refl
scMultZeroRight Same = Refl
scMultZeroRight Unknown = Refl

scMultAssociative : (a, b, c : SizeChange) -> a |*| (b |*| c) = (a |*| b) |*| c
scMultAssociative Smaller Smaller Smaller = Refl
scMultAssociative Same b c = Refl
scMultAssociative a Same c =
  rewrite scMultNeutralRight a in
  Refl
scMultAssociative a b Same =
  rewrite scMultNeutralRight b in
  rewrite scMultNeutralRight (a |*| b) in
  Refl
scMultAssociative Unknown b c = Refl
scMultAssociative a Unknown c =
  rewrite scMultZeroRight a in
  Refl
scMultAssociative a b Unknown =
  rewrite scMultZeroRight b in
  rewrite scMultZeroRight a in
  rewrite scMultZeroRight (a |*| b) in
  Refl

scMultCommutative : (a, b : SizeChange) -> a |*| b = b |*| a
scMultCommutative Smaller Smaller = Refl
scMultCommutative b Same =
  rewrite scMultNeutralRight b in
  Refl
scMultCommutative Smaller Unknown = Refl
scMultCommutative Same b =
  rewrite scMultNeutralRight b in
  Refl
scMultCommutative Unknown b =
 rewrite scMultZeroRight b in
 Refl

scPlusIdempotent : (a : SizeChange) -> a |+| a = a
scPlusIdempotent Smaller = Refl
scPlusIdempotent Same = Refl
scPlusIdempotent Unknown = Refl

scMultPlusDist : (a, b, c : SizeChange) -> a |*| (b |+| c) = (a |*| b) |+| (a |*| c)
scMultPlusDist Unknown b c = Refl
scMultPlusDist a Unknown c =
  rewrite scMultZeroRight a in
  Refl
scMultPlusDist a b Unknown =
  rewrite scPlusNeutralRight b in
  rewrite scMultZeroRight a in
  rewrite scPlusNeutralRight (a |*| b) in
  Refl
scMultPlusDist Same b c = Refl
scMultPlusDist a Same Same =
  rewrite scMultNeutralRight a in
  rewrite scPlusIdempotent a in
  Refl
scMultPlusDist Smaller Same Smaller = Refl
scMultPlusDist Smaller Smaller Same = Refl
scMultPlusDist Smaller Smaller Smaller = Refl

export
Pretty Void SizeChange where
  pretty Smaller = pretty "<"
  pretty Same = pretty "="
  pretty Unknown = neutral
