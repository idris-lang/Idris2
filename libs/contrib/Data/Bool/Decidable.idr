module Data.Bool.Decidable

import Decidable.Equality
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
invert : {0 b : Bool} -> {0 p : Type} -> Reflects p b -> case b of {True => p; False => Not p}
invert {b = True} (RTrue  x ) = x
invert {b = False} (RFalse nx) = nx

public export
remember : {b : Bool} -> {0 p : Type} -> case b of {True => p; False => Not p} -> Reflects p b
remember {b = True } = RTrue 
remember {b = False} = RFalse
