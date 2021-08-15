module Control.Algebra.Laws

import Control.Algebra

%default total

-- Monoids

||| Inverses are unique.
public export
uniqueInverse : MonoidV ty => (x, y, z : ty) ->
  y <+> x = neutral {ty} -> x <+> z = neutral {ty} -> y = z
uniqueInverse x y z p q =
  rewrite sym $ monoidNeutralIsNeutralL y in
    rewrite sym q in
      rewrite semigroupOpIsAssociative y x z in
  rewrite p in
    rewrite monoidNeutralIsNeutralR z in
      Refl

-- Groups

||| Only identity is self-squaring.
public export
selfSquareId : Group ty => (x : ty) ->
  x <+> x = x -> x = neutral {ty}
selfSquareId x p =
  rewrite sym $ monoidNeutralIsNeutralR x in
    rewrite sym $ groupInverseIsInverseR x in
  rewrite sym $ semigroupOpIsAssociative (inverse x) x x in
    rewrite p in
      Refl

||| Inverse elements commute.
public export
inverseCommute : Group ty => (x, y : ty) ->
  y <+> x = neutral {ty} -> x <+> y = neutral {ty}
inverseCommute x y p = selfSquareId (x <+> y) prop where
  prop : (x <+> y) <+> (x <+> y) = x <+> y
  prop =
    rewrite sym $ semigroupOpIsAssociative x y (x <+> y) in
      rewrite semigroupOpIsAssociative y x y in
    rewrite p in
      rewrite monoidNeutralIsNeutralR y in
        Refl

||| Every element has a right inverse.
public export
groupInverseIsInverseL : Group ty => (x : ty) ->
  x <+> inverse x = neutral {ty}
groupInverseIsInverseL x =
  inverseCommute x (inverse x) (groupInverseIsInverseR x)

||| -(-x) = x
public export
inverseSquaredIsIdentity : Group ty => (x : ty) ->
  inverse (inverse x) = x
inverseSquaredIsIdentity {ty} x =
  uniqueInverse
    (inverse x)
    (inverse $ inverse x)
    x
    (groupInverseIsInverseR $ inverse x)
    (groupInverseIsInverseR x)

||| If every square in a group is identity, the group is commutative.
public export
squareIdCommutative : Group ty => (x, y : ty) ->
  ((a : ty) -> a <+> a = neutral {ty}) ->
  x <+> y = y <+> x
squareIdCommutative x y p =
  uniqueInverse (x <+> y) (x <+> y) (y <+> x) (p (x <+> y)) prop where
    prop : (x <+> y) <+> (y <+> x) = neutral {ty}
    prop =
      rewrite sym $ semigroupOpIsAssociative x y (y <+> x) in
        rewrite semigroupOpIsAssociative y y x in
      rewrite p y in
        rewrite monoidNeutralIsNeutralR x in
          p x

||| -0 = 0
public export
inverseNeutralIsNeutral : Group ty =>
  inverse (neutral {ty}) = neutral {ty}
inverseNeutralIsNeutral {ty} =
  rewrite sym $ cong inverse (groupInverseIsInverseL (neutral {ty})) in
    rewrite monoidNeutralIsNeutralR $ inverse (neutral {ty}) in
      inverseSquaredIsIdentity (neutral {ty})

-- ||| -(x + y) = -y + -x
-- public export
-- inverseOfSum : Group ty => (l, r : ty) ->
--   inverse (l <+> r) = inverse r <+> inverse l
-- inverseOfSum {ty} l r =
--   -- expand
--   rewrite sym $ monoidNeutralIsNeutralR $ inverse $ l <+> r in
--     rewrite sym $ groupInverseIsInverseR r in
--       rewrite sym $ monoidNeutralIsNeutralL $ inverse r in
--         rewrite sym $ groupInverseIsInverseR l in
--   -- shuffle
--   rewrite semigroupOpIsAssociative (inverse r) (inverse l) l in
--     rewrite sym $ semigroupOpIsAssociative (inverse r <+> inverse l) l r in
--       rewrite sym $ semigroupOpIsAssociative (inverse r <+> inverse l) (l <+> r) (inverse $ l <+> r) in
--   -- contract
--   rewrite sym $ monoidNeutralIsNeutralL $ inverse l in
--     rewrite groupInverseIsInverseL $ l <+> r in
--       rewrite sym $ semigroupOpIsAssociative (inverse r <+> (inverse l <+> neutral)) l (inverse l <+> neutral) in
--         rewrite semigroupOpIsAssociative l (inverse l) neutral in
--           rewrite groupInverseIsInverseL l in
--             rewrite monoidNeutralIsNeutralL $ the ty neutral in
--               Refl

||| y = z if x + y = x + z
public export
cancelLeft : Group ty => (x, y, z : ty) ->
  x <+> y = x <+> z -> y = z
cancelLeft x y z p =
  rewrite sym $ monoidNeutralIsNeutralR y in
    rewrite sym $ groupInverseIsInverseR x in
      rewrite sym $ semigroupOpIsAssociative (inverse x) x y in
        rewrite p in
      rewrite semigroupOpIsAssociative (inverse x) x z in
    rewrite groupInverseIsInverseR x in
  monoidNeutralIsNeutralR z

||| y = z if y + x = z + x.
public export
cancelRight : Group ty => (x, y, z : ty) ->
  y <+> x = z <+> x -> y = z
cancelRight x y z p =
  rewrite sym $ monoidNeutralIsNeutralL y in
    rewrite sym $ groupInverseIsInverseL x in
      rewrite semigroupOpIsAssociative y x (inverse x) in
        rewrite p in
      rewrite sym $ semigroupOpIsAssociative z x (inverse x) in
    rewrite groupInverseIsInverseL x in
  monoidNeutralIsNeutralL z

||| ab = 0 -> a = b^-1
public export
neutralProductInverseR : Group ty => (a, b : ty) ->
  a <+> b = neutral {ty} -> a = inverse b
neutralProductInverseR a b prf =
  cancelRight  b a (inverse b) $
    trans prf $ sym $ groupInverseIsInverseR b

||| ab = 0 -> a^-1 = b
public export
neutralProductInverseL : Group ty => (a, b : ty) ->
  a <+> b = neutral {ty} -> inverse a = b
neutralProductInverseL a b prf =
  cancelLeft a (inverse a) b $
    trans (groupInverseIsInverseL a) $ sym prf

||| For any a and b, ax = b and ya = b have solutions.
public export
latinSquareProperty : Group ty => (a, b : ty) ->
  ((x : ty ** a <+> x = b),
    (y : ty ** y <+> a = b))
latinSquareProperty a b =
  ((((inverse a) <+> b) **
    rewrite semigroupOpIsAssociative a (inverse a) b in
      rewrite groupInverseIsInverseL a in
        monoidNeutralIsNeutralR b),
  (b <+> (inverse a) **
    rewrite sym $ semigroupOpIsAssociative b (inverse a) a in
      rewrite groupInverseIsInverseR a in
        monoidNeutralIsNeutralL b))

||| For any a, b, x, the solution to ax = b is unique.
public export
uniqueSolutionR : Group ty => (a, b, x, y : ty) ->
  a <+> x = b -> a <+> y = b -> x = y
uniqueSolutionR a b x y p q = cancelLeft a x y $ trans p (sym q)

||| For any a, b, y, the solution to ya = b is unique.
public export
uniqueSolutionL : Group t => (a, b, x, y : t) ->
  x <+> a = b -> y <+> a = b -> x = y
uniqueSolutionL a b x y p q = cancelRight a x y $ trans p (sym q)

-- ||| -(x + y) = -x + -y
-- public export
-- inverseDistributesOverGroupOp : AbelianGroup ty => (l, r : ty) ->
--   inverse (l <+> r) = inverse l <+> inverse r
-- inverseDistributesOverGroupOp l r =
--   rewrite groupOpIsCommutative (inverse l) (inverse r) in
--     inverseOfSum l r

||| Homomorphism preserves neutral.
public export
homoNeutral : GroupHomomorphism a b =>
  to (neutral {ty=a}) = neutral {ty=b}
homoNeutral =
  selfSquareId (to neutral) $
    trans (sym $ toGroup neutral neutral) $
      cong to $ monoidNeutralIsNeutralL neutral

||| Homomorphism preserves inverses.
public export
homoInverse : GroupHomomorphism a b => (x : a) ->
  the b (to $ inverse x) = the b (inverse $ to x)
homoInverse x =
  cancelRight (to x) (to $ inverse x) (inverse $ to x) $
    trans (sym $ toGroup (inverse x) x) $
      trans (cong to $ groupInverseIsInverseR x) $
        trans homoNeutral $
          sym $ groupInverseIsInverseR (to x)

-- Rings

||| 0x = x
public export
multNeutralAbsorbingL : Ring ty => (r : ty) ->
  neutral {ty} <.> r = neutral {ty}
multNeutralAbsorbingL {ty} r =
  rewrite sym $ monoidNeutralIsNeutralR $ neutral <.> r in
    rewrite sym $ groupInverseIsInverseR $ neutral <.> r in
  rewrite sym $ semigroupOpIsAssociative (inverse $ neutral <.> r) (neutral <.> r) (((inverse $ neutral <.> r) <+> (neutral <.> r)) <.> r) in
    rewrite groupInverseIsInverseR $ neutral <.> r in
  rewrite sym $ ringOpIsDistributiveR neutral neutral r in
    rewrite monoidNeutralIsNeutralR $ the ty neutral in
  groupInverseIsInverseR $ neutral <.> r

||| x0 = 0
public export
multNeutralAbsorbingR : Ring ty => (l : ty) ->
  l <.> neutral {ty} = neutral {ty}
multNeutralAbsorbingR {ty} l =
  rewrite sym $ monoidNeutralIsNeutralL $ l <.> neutral in
    rewrite sym $ groupInverseIsInverseL $ l <.> neutral in
  rewrite semigroupOpIsAssociative (l <.> ((l <.> neutral) <+> (inverse $ l <.> neutral))) (l <.> neutral) (inverse $ l <.> neutral) in
    rewrite groupInverseIsInverseL $ l <.> neutral in
  rewrite sym $ ringOpIsDistributiveL l neutral neutral in
    rewrite monoidNeutralIsNeutralL $ the ty neutral in
  groupInverseIsInverseL $ l <.> neutral

||| (-x)y = -(xy)
public export
multInverseInversesL : Ring ty => (l, r : ty) ->
  inverse l <.> r = inverse (l <.> r)
multInverseInversesL l r =
  rewrite sym $ monoidNeutralIsNeutralR $ inverse l <.> r in
    rewrite sym $ groupInverseIsInverseR $ l <.> r in
      rewrite sym $ semigroupOpIsAssociative (inverse $ l <.> r) (l <.> r) (inverse l <.> r) in
  rewrite sym $ ringOpIsDistributiveR l (inverse l) r in
    rewrite groupInverseIsInverseL l in
  rewrite multNeutralAbsorbingL r in
    monoidNeutralIsNeutralL $ inverse $ l <.> r

||| x(-y) = -(xy)
public export
multInverseInversesR : Ring ty => (l, r : ty) ->
  l <.> inverse r = inverse (l <.> r)
multInverseInversesR l r =
  rewrite sym $ monoidNeutralIsNeutralL $ l <.> (inverse r) in
    rewrite sym $ groupInverseIsInverseL (l <.> r) in
      rewrite semigroupOpIsAssociative (l <.> (inverse r)) (l <.> r) (inverse $ l <.> r) in
  rewrite sym $ ringOpIsDistributiveL l (inverse r) r in
    rewrite groupInverseIsInverseR r in
  rewrite multNeutralAbsorbingR l in
    monoidNeutralIsNeutralR $ inverse $ l <.> r

||| (-x)(-y) = xy
public export
multNegativeByNegativeIsPositive : Ring ty => (l, r : ty) ->
  inverse l <.> inverse r = l <.> r
multNegativeByNegativeIsPositive l r =
    rewrite multInverseInversesR (inverse l) r in
    rewrite sym $ multInverseInversesL (inverse l) r in
    rewrite inverseSquaredIsIdentity l in
    Refl

||| (-1)x = -x
public export
inverseOfUnityR : RingWithUnity ty => (x : ty) ->
  inverse (unity {ty}) <.> x = inverse x
inverseOfUnityR x =
  rewrite multInverseInversesL unity x in
    rewrite unityIsRingIdR x in
      Refl

||| x(-1) = -x
public export
inverseOfUnityL : RingWithUnity ty => (x : ty) ->
  x <.> inverse (unity {ty}) = inverse x
inverseOfUnityL x =
  rewrite multInverseInversesR x unity in
    rewrite unityIsRingIdL x in
      Refl
