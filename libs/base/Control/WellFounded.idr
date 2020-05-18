module Control.WellFounded

import Data.Nat
import Data.List

public export
data Accessible : (rel : a -> a -> Type) -> (x : a) -> Type where
  Access : (rec : (y : a) -> rel y x -> Accessible rel y) ->
           Accessible rel x

public export
interface WellFounded (rel : a -> a -> Type) where
  wellFounded : (x : a) -> Accessible rel x

export
accRec : {0 rel : (arg1 : a) -> (arg2 : a) -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
         (z : a) -> (0 acc : Accessible rel z) -> b
accRec step z (Access f) =
  step z $ \yarg, lt => accRec step yarg (f yarg lt)

export
accInd : {0 rel : a -> a -> Type} -> {0 P : a -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
         (z : a) -> (0 acc : Accessible rel z) -> P z
accInd step z (Access f) =
  step z $ \y, lt => accInd step y (f y lt)

export
wfRec : WellFounded rel =>
        (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
        a -> b
wfRec step x = accRec step x (wellFounded {rel} x)

export
wfInd : WellFounded rel => {0 P : a -> Type} ->
        (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
        (myz : a) -> P myz
wfInd step myz = accInd step myz (wellFounded {rel} myz)

public export
interface Sized a where
  size : a -> Nat

public export
Smaller : Sized a => a -> a -> Type
Smaller x y = size x `LT` size y

public export
SizeAccessible : Sized a => a -> Type
SizeAccessible = Accessible Smaller

export
sizeAccessible : Sized a => (x : a) -> SizeAccessible x
sizeAccessible x = Access (acc $ size x)
  where
    acc : (sizeX : Nat) -> (y : a) -> (size y `LT` sizeX) -> SizeAccessible y
    acc (S x') y (LTESucc yLEx')
        = Access (\z, zLTy => acc x' z (lteTransitive zLTy yLEx'))

export
sizeInd : Sized a => {0 P : a -> Type} ->
          (step : (x : a) -> ((y : a) -> Smaller y x -> P y) -> P x) ->
          (z : a) ->
          P z
sizeInd step z = accInd step z (sizeAccessible z)

export
sizeRec : Sized a =>
          (step : (x : a) -> ((y : a) -> Smaller y x -> b) -> b) ->
          (z : a) -> b
sizeRec step z = accRec step z (sizeAccessible z)

export
implementation Sized Nat where
  size = \x => x

export
implementation Sized (List a) where
  size = length

export
implementation (Sized a, Sized b) => Sized (Pair a b) where
  size (x,y) = size x + size y
