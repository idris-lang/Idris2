module Control.Function.FunExt

%default total

||| This interface contains a proposition for the function extensionality.
||| It is not meant to be ever implemented.
||| It can be used to mark properties as requiring function extensionality to hold,
||| i.e. its main objective is to provide a universal way to formulate a conditional property
||| that holds only in the presence of function extensionality.
public export
interface FunExt where
  0 funExt : {0 f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g
