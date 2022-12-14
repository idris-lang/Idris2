import Syntax.PreorderReasoning

-------- some notation ----------
infixr 6 .+.,:+:
infixr 7 .*.,:*:

interface Additive a where
  constructor MkAdditive
  (.+.) : a -> a -> a
  O   : a

interface Additive2 a where
  constructor MkAdditive2
  (:+:) : a -> a -> a
  O2   : a

interface Multiplicative a where
  constructor MkMultiplicative
  (.*.) : a -> a -> a
  I     : a

record MonoidOver U where
  constructor WithStruct
  Unit    : U
  Mult    : U -> U -> U
  lftUnit : (x : U) -> Unit `Mult` x    = x
  rgtUnit : (x : U) -> x    `Mult` Unit = x
  assoc   : (x,y,z : U)
                    -> x `Mult` (y `Mult` z) = (x `Mult` y) `Mult` z

record Monoid where
  constructor MkMonoid
  U : Type
  Struct : MonoidOver U

AdditiveStruct : (m : MonoidOver a) -> Additive a
AdditiveStruct m = MkAdditive (Mult $ m)
                              (Unit $ m)
AdditiveStruct2 : (m : MonoidOver a) -> Additive2 a
AdditiveStruct2 m = MkAdditive2 (Mult $ m)
                                (Unit $ m)
AdditiveStructs : (ma : MonoidOver a) -> (mb : MonoidOver b)
              -> (Additive a, Additive2 b)
AdditiveStructs ma mb = (AdditiveStruct ma, AdditiveStruct2 mb)

getAdditive : (m : Monoid) -> Additive (U m)
getAdditive m = AdditiveStruct (Struct m)

MultiplicativeStruct : (m : Monoid) -> Multiplicative (U m)
MultiplicativeStruct m = MkMultiplicative (Mult $ Struct m)
                                          (Unit $ Struct m)
-----------------------------------------------------

0 Commutative : MonoidOver a -> Type
Commutative m = (x,y : a) -> let _ = AdditiveStruct m in
                x .+. y = y .+. x

0 Commute : (Additive a, Additive2 a) => Type
Commute =
          (x11,x12,x21,x22 : a) ->
          ((x11 :+: x12) .+. (x21 :+: x22))
          =
          ((x11 .+. x21) :+: (x12 .+. x22))

product : (ma, mb : Monoid) -> Monoid
product ma mb =
  let
      %hint aStruct : Additive (U ma)
      aStruct = getAdditive ma
      %hint bStruct : Additive (U mb)
      bStruct = getAdditive mb

  in MkMonoid (U ma, U mb) $ WithStruct
     (O, O)
     (\(x1,y1), (x2, y2)  => (x1 .+. x2, y1 .+. y2))
     (\(x,y) => rewrite lftUnit (Struct ma) x in
                rewrite lftUnit (Struct mb) y in
                Refl)
     (\(x,y) => rewrite rgtUnit (Struct ma) x in
                rewrite rgtUnit (Struct mb) y in
                Refl)
     (\(x1,y1),(x2,y2),(x3,y3) =>
                rewrite assoc (Struct ma) x1 x2 x3 in
                rewrite assoc (Struct mb) y1 y2 y3 in
                Refl)

EckmannHilton : forall a . (ma,mb : MonoidOver a)
             -> let ops = AdditiveStructs ma mb in
                Commute @{ops}
             -> (Commutative ma, (x,y : a) -> x .+. y = x :+: y)
EckmannHilton ma mb prf =
  let %hint first : Additive a
      first = AdditiveStruct ma
      %hint second : Additive2 a
      second = AdditiveStruct2 mb in
  let SameUnits : (the a O === O2)
      SameUnits = Calc $
        |~ O
        ~~  O         .+.         O  ...(sym $ lftUnit ma O)
        ~~ (O :+: O2) .+. (O2 :+: O) ...(sym $ cong2 (.+.)
                                             (rgtUnit mb O)
                                             (lftUnit mb O))
        ~~ (O .+. O2) :+: (O2 .+. O) ...(prf O O2 O2 O)
        ~~        O2  :+:  O2        ...(cong2 (:+:)
                                             (lftUnit ma O2)
                                             (rgtUnit ma O2))
        ~~ O2                        ...(lftUnit mb O2)

      SameMults : (x,y : a) -> (x .+. y) === (x :+: y)
      SameMults x y = Calc $
        |~ x .+. y
        ~~ (x :+: O2) .+. (O2 :+: y) ...(sym $ cong2 (.+.)
                                             (rgtUnit mb x)
                                             (lftUnit mb y))
        ~~ (x .+. O2) :+: (O2 .+. y) ...(prf x O2 O2 y)
        ~~ (x .+. O ) :+: (O  .+. y) ...(cong (\u =>
                                              (x .+. u) :+: (u .+. y))
                                              (sym SameUnits))
        ~~ x :+: y                   ...(cong2 (:+:)
                                              (rgtUnit ma x)
                                              (lftUnit ma y))

      Commutativity : Commutative ma
      Commutativity x y = Calc $
        |~ x .+. y
        ~~ (O2 :+: x) .+. (y :+: O2) ...(sym $ cong2 (.+.)
                                             (lftUnit mb x)
                                             (rgtUnit mb y))
        ~~ (O2 .+. y) :+: (x .+. O2) ...(prf O2 x y O2)
        ~~ (O  .+. y) :+: (x .+. O ) ...(cong (\u =>
                                              (u .+. y) :+: (x .+. u))
                                              (sym SameUnits))
        ~~ y :+: x                   ...(cong2 (:+:)
                                              (lftUnit ma y)
                                              (rgtUnit ma x))
        ~~ y .+. x                   ...(sym $ SameMults y x)
  in (Commutativity, SameMults)
