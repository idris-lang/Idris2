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

export
funExt0 : FunExt => {0 b : a -> Type} -> {0 f, g : (0 x : a) -> b x} -> ((x : a) -> f x = g x) -> f = g
funExt0 prf = rewrite funExt {f = \x => f x} {g = \y => g y} prf in Refl

export
funExt1 : FunExt => {0 b : a -> Type} -> {0 f, g : (1 x : a) -> b x} -> ((x : a) -> f x = g x) -> f = g
funExt1 prf = rewrite funExt {f = \x => f x} {g = \y => g y} prf in Refl
