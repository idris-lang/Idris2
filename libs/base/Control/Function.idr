module Control.Function

%default total

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
    injective = injective . injective

||| If (g . f) is injective, so is f.
public export
[InjFromComp] {f : a -> b} -> {g : b -> c} ->
  Injective (g . f) => Injective f where
    injective prf = injective {f = (g . f)} $ cong g prf

public export
[IdInjective] Injective Prelude.id where
  injective = id

----------------------------------------

||| An bi-injective function maps distinct elements to distinct elements in both arguments.
||| This is more strict than injectivity on each of arguments.
||| For instance, list appending is injective on both arguments but is not biinjective.
public export
interface Biinjective (0 f : a -> b -> c) | f where
  constructor MkBiinjective
  biinjective : {x, y : a} -> {v, w : b} -> f x v = f y w -> (x = y, v = w)

public export
biinj : (0 f : _) -> (0 _ : Biinjective f) => (0 _ : f x v = f y w) -> (x = y, v = w)
biinj _ eq = let 0 bii = biinjective eq in (irrelevantEq $ fst bii, irrelevantEq $ snd bii)

public export
[ComposeBiinjective] {f : a -> b -> c} -> {g : c -> d} ->
  Biinjective f => Injective g => Biinjective (g .: f) where
    biinjective = biinjective . injective

||| If (g .: f) is biinjective, so is f.
public export
[BiinjFromComp] {f : a -> b -> c} -> {g : c -> d} ->
  Biinjective (g .: f) => Biinjective f where
    biinjective = biinjective {f = (g .: f)} . cong g

public export
[FlipBiinjective] {f : a -> b -> c} ->
  Biinjective f => Biinjective (flip f) where
    biinjective = swap . biinjective

public export
[FromBiinjectiveL] {f : a -> b -> c} -> {x : a} ->
  Biinjective f => Injective (f x) where
    injective = snd . biinjective

public export
[FromBiinjectiveR] {f : a -> b -> c} -> {y : b} ->
  Biinjective f => Injective (`f` y) where
    injective = fst . biinjective

export
Biinjective MkPair where
  biinjective Refl = (Refl, Refl)
