module Control.Function.FunExt

%default total

||| This interface contains a proposition for the function extensionality.
||| It is not meant to be ever implemented.
||| It can be used to mark properties as requiring function extensionality to hold,
||| i.e. its main objective is to provide a universal way to formulate a conditional property
||| that holds only in the presence of function extensionality.
public export
interface FunExt where
  funExt : {0 b : a -> Type} -> {0 f, g : (x : a) -> b x} -> ((x : a) -> f x = g x) -> f = g
