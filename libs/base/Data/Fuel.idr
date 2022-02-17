module Data.Fuel

%default total

||| Fuel for running total operations potentially indefinitely.
public export
data Fuel = Dry | More (Lazy Fuel)

||| Provide `n` units of fuel.
public export
limit : Nat -> Fuel
limit  Z    = Dry
limit (S n) = More (limit n)

||| Provide fuel indefinitely.
||| This function is fundamentally partial.
export
covering
forever : Fuel
forever = More forever
