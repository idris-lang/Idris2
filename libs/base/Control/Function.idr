module Control.Function

||| An injective function maps distinct elements to distinct elements.
public export
interface Injective (f : a -> b) | f where
  constructor MkInjective
  injective : {x, y : a} -> f x = f y -> x = y

public export
inj : (0 f : a -> b) -> {auto 0 _ : Injective f} -> {0 x, y : a} -> (0 _ : f x = f y) -> x = y
inj _ eq = irrelevantEq (injective eq)

----------------------------------------

||| The composition of injective functions is injective.
public export
[ComposeInjective] {f : a -> b} -> {g : b -> c} ->
  (Injective f, Injective g) => Injective (g . f) where
    injective prf = injective $ injective prf

||| If (g . f) is injective, so is f.
public export
[InjFromComp] {f : a -> b} -> {g : b -> c} ->
  Injective (g . f) => Injective f where
    injective prf = injective {f = (g . f)} $ cong g prf

public export
[IdInjective] Injective Prelude.id where
  injective = id
