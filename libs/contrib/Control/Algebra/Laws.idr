module Control.Algebra.Laws

import Prelude
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
-- inverseSquaredIsIdentity x =
--   let x' = inverse x in
--     uniqueInverse
--       x'
--       (inverse x')
--       x
--       (groupInverseIsInverseR x')
--       (groupInverseIsInverseR x)

||| If every square in a group is identity, the group is commutative.
public export
squareIdCommutative : Group ty => (x, y : ty) ->
  ((a : ty) -> a <+> a = neutral {ty}) ->
  x <+> y = y <+> x
-- squareIdCommutative x y p =
--   let
--     xy = x <+> y
--     yx = y <+> x
--       in
--   uniqueInverse xy xy yx (p xy) prop where
--     prop : (x <+> y) <+> (y <+> x) = neutral {ty}
--     prop =
--       rewrite sym $ semigroupOpIsAssociative x y (y <+> x) in
--         rewrite semigroupOpIsAssociative y y x in
--       rewrite p y in
--         rewrite monoidNeutralIsNeutralR x in
--           p x

||| -0 = 0
public export
inverseNeutralIsNeutral : Group ty =>
  inverse (neutral {ty}) = neutral {ty}
-- inverseNeutralIsNeutral {ty} =
--   let e = neutral {ty} in
--     rewrite sym $ cong inverse (groupInverseIsInverseL e) in
--       rewrite monoidNeutralIsNeutralR $ inverse e in
--         inverseSquaredIsIdentity e

||| -(x + y) = -y + -x
public export
inverseOfSum : Group ty => (l, r : ty) ->
  inverse (l <+> r) = inverse r <+> inverse l
-- inverseOfSum {ty} l r =
--   let
--     e = neutral {ty}
--     il = inverse l
--     ir = inverse r
--     lr = l <+> r
--     ilr = inverse lr
--     iril = ir <+> il
--     ile = il <+> e
--       in
--   -- expand
--   rewrite sym $ monoidNeutralIsNeutralR ilr in
--     rewrite sym $ groupInverseIsInverseR r in
--       rewrite sym $ monoidNeutralIsNeutralL ir in
--         rewrite sym $ groupInverseIsInverseR l in
--   -- shuffle
--   rewrite semigroupOpIsAssociative ir il l in
--     rewrite sym $ semigroupOpIsAssociative iril l r in
--       rewrite sym $ semigroupOpIsAssociative iril lr ilr in
--   -- contract
--   rewrite sym $ monoidNeutralIsNeutralL il in
--     rewrite groupInverseIsInverseL lr in
--       rewrite sym $ semigroupOpIsAssociative (ir <+> ile) l ile in
--         rewrite semigroupOpIsAssociative l il e in
--           rewrite groupInverseIsInverseL l in
--             rewrite monoidNeutralIsNeutralL e in
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
-- latinSquareProperty a b =
--   let a' = inverse a in
--     (((a' <+> b) **
--       rewrite semigroupOpIsAssociative a a' b in
--         rewrite groupInverseIsInverseL a in
--           monoidNeutralIsNeutralR b),
--     (b <+> a' **
--       rewrite sym $ semigroupOpIsAssociative b a' a in
--         rewrite groupInverseIsInverseR a in
--           monoidNeutralIsNeutralL b))

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

||| -(x + y) = -x + -y
public export
inverseDistributesOverGroupOp : AbelianGroup ty => (l, r : ty) ->
  inverse (l <+> r) = inverse l <+> inverse r
inverseDistributesOverGroupOp l r =
  rewrite groupOpIsCommutative (inverse l) (inverse r) in
    inverseOfSum l r

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
-- multNeutralAbsorbingL {ty} r =
--   let
--     e = neutral {ty}
--     ir = inverse r
--     exr = e <.> r
--     iexr = inverse exr
--       in
--   rewrite sym $ monoidNeutralIsNeutralR exr in
--     rewrite sym $ groupInverseIsInverseR exr in
--   rewrite sym $ semigroupOpIsAssociative iexr exr ((iexr <+> exr) <.> r) in
--     rewrite groupInverseIsInverseR exr in
--   rewrite sym $ ringOpIsDistributiveR e e r in
--     rewrite monoidNeutralIsNeutralR e in
--   groupInverseIsInverseR exr

||| x0 = 0
public export
multNeutralAbsorbingR : Ring ty => (l : ty) ->
  l <.> neutral {ty} = neutral {ty}
-- multNeutralAbsorbingR {ty} l =
--   let
--     e = neutral {ty}
--     il = inverse l
--     lxe = l <.> e
--     ilxe = inverse lxe
--       in
--   rewrite sym $ monoidNeutralIsNeutralL lxe in
--     rewrite sym $ groupInverseIsInverseL lxe in
--   rewrite semigroupOpIsAssociative (l <.> (lxe <+> ilxe)) lxe ilxe in
--     rewrite groupInverseIsInverseL lxe in
--   rewrite sym $ ringOpIsDistributiveL l e e in
--     rewrite monoidNeutralIsNeutralL e in
--   groupInverseIsInverseL lxe

||| (-x)y = -(xy)
public export
multInverseInversesL : Ring ty => (l, r : ty) ->
  inverse l <.> r = inverse (l <.> r)
-- multInverseInversesL l r =
--   let
--     il = inverse l
--     lxr = l <.> r
--     ilxr = il <.> r
--     i_lxr = inverse lxr
--       in
--   rewrite sym $ monoidNeutralIsNeutralR ilxr in
--     rewrite sym $ groupInverseIsInverseR lxr in
--       rewrite sym $ semigroupOpIsAssociative i_lxr lxr ilxr in
--   rewrite sym $ ringOpIsDistributiveR l il r in
--     rewrite groupInverseIsInverseL l in
--   rewrite multNeutralAbsorbingL r in
--     monoidNeutralIsNeutralL i_lxr

||| x(-y) = -(xy)
public export
multInverseInversesR : Ring ty => (l, r : ty) ->
  l <.> inverse r = inverse (l <.> r)
-- multInverseInversesR l r =
--   let
--     ir = inverse r
--     lxr = l <.> r
--     lxir = l <.> ir
--     ilxr = inverse lxr
--       in
--   rewrite sym $ monoidNeutralIsNeutralL lxir in
--     rewrite sym $ groupInverseIsInverseL lxr in
--       rewrite semigroupOpIsAssociative lxir lxr ilxr in
--   rewrite sym $ ringOpIsDistributiveL l ir r in
--     rewrite groupInverseIsInverseR r in
--   rewrite multNeutralAbsorbingR l in
--     monoidNeutralIsNeutralR ilxr

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
