module Data.Linear.Interface

import Data.Linear.Notation
import public Data.Linear.Copies

||| An interface for consumable types
public export
interface Consumable a where
  consume : a -@ ()

||| Void and the unit type are trivially consumable
export
Consumable Void where consume v impossible

export
Consumable () where consume u = u
-- But crucially we don't have `Consumable World` or `Consumable Handle`.

infixr 5 `seq`
||| We can sequentially compose a computation returning a value that is
||| consumable with another computation. This is done by first consuming
||| the result of the first computation and then returning the second one.
export
seq : Consumable a => a -@ b -@ b
a `seq` b = let 1 () = consume a in b

||| Unions can be consumed by pattern matching
export
Consumable Bool where
  consume True = ()
  consume False = ()

||| We can cheat to make built-in types consumable
export
Consumable Int where
  consume = believe_me (\ 0 i : Int => ())

public export
interface Duplicable a where
  duplicate : (1 v : a) -> 2 `Copies` v

export
Duplicable Void where
  duplicate Void impossible

export
Duplicable () where
  duplicate () = [(), ()]

||| Comonoid is the dual of Monoid, it can consume a value linearly and duplicate a value linearly
public export
interface Comonoid a where
  counit : a -@ ()
  comult : (1 v : a) -> 2 `Copies` v

export
Consumable a => Duplicable a => Comonoid a where
  counit = consume
  comult = duplicate

export
Comonoid (!* a) where
  counit (MkBang _) = ()
  comult (MkBang v) = [MkBang v , MkBang v]

