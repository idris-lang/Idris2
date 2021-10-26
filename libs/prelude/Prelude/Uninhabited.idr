module Prelude.Uninhabited

import Builtin
import Prelude.Basics

%default total

||| A canonical proof that some type is empty.
public export
interface Uninhabited t where
  constructor MkUninhabited
  ||| If I have a t, I've had a contradiction.
  ||| @ t the uninhabited type
  uninhabited : t -> Void

%extern
prim__void : (0 x : Void) -> a

||| The eliminator for the `Void` type.
public export
void : (0 x : Void) -> a
void = prim__void

export
Uninhabited Void where
  uninhabited = id

||| Use an absurd assumption to discharge a proof obligation.
||| @ t some empty type
||| @ a the goal type
||| @ h the contradictory hypothesis
public export
absurd : Uninhabited t => (h : t) -> a
absurd h = void (uninhabited h)

public export
Uninhabited (True = False) where
  uninhabited Refl impossible

public export
Uninhabited (False = True) where
  uninhabited Refl impossible
