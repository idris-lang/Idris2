--- Data declarations ---

infix 0 =%=

public export
data (=%=) : (a -> b) -> (a -> b) -> Type where
  ExtEq : {0 f, g : a -> b} -> ((x : a) -> f x = g x) -> f =%= g

infix 0 %%

public export
data (%%) a b = Equs (a = b) (b = a)

--- Records ---

infix 0 =%%=

public export
record (=%%=) {a : Type} {b : Type} (f : a -> b) (g : a -> b) where
  constructor ExtEqR
  fa : (x : a) -> f x = g x

--- Interfaces ---

infix 0 =%%%=

public export
interface (=%%%=) (x : a) (y : a) (b : Type) (i : Type) where
  idx : a -> i -> b
  eq : (ix : i) -> idx x ix = idx y ix
