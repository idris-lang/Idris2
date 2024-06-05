module Data.Bool.Decidable

import Data.Void

public export
data Reflects : Type -> Bool -> Type where
  RTrue  :     p -> Reflects p True
  RFalse : Not p -> Reflects p False

public export
recompute : Dec a -> (0 x : a) -> a
recompute (Yes x) _ = x
recompute (No contra) x = absurdity $ contra x

public export
invert : {0 b : Bool} -> {0 p : Type} -> Reflects p b -> if b then p else Not p
invert {b = True} (RTrue  x ) = x
invert {b = False} (RFalse nx) = nx

public export
remember : {b : Bool} -> {0 p : Type} -> (if b then p else Not p) -> Reflects p b
remember {b = True } = RTrue
remember {b = False} = RFalse

public export
reflect : {c : Bool} -> Reflects p b -> (if c then p else Not p) -> b = c
reflect {c = True } (RTrue   x)  _ = Refl
reflect {c = True } (RFalse nx)  x = absurd $ nx x
reflect {c = False} (RTrue   x) nx = absurd $ nx x
reflect {c = False} (RFalse nx)  _ = Refl
