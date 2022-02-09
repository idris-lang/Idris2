module Data.Linear.Interface

import Data.Linear.Notation
import Data.Linear.Bifunctor
import public Data.Linear.Copies

%default total

||| An interface for consumable types
public export
interface Consumable a where
  consume : a -@ ()

||| Void and the unit type are trivially consumable
export
Consumable Void where consume v impossible

export
Consumable () where consume u = u

||| Unions can be consumed by pattern matching
export
Consumable Bool where
  consume True = ()
  consume False = ()

export
Consumable (!* a) where
  consume (MkBang v) = ()

||| We can cheat to make built-in types consumable
export
Consumable Int where
  consume = believe_me (\ 0 i : Int => ())

-- But crucially we don't have `Consumable World` or `Consumable Handle`.

infixr 5 `seq`
||| We can sequentially compose a computation returning a value that is
||| consumable with another computation. This is done by first consuming
||| the result of the first computation and then returning the second one.
export
seq : Consumable a => a -@ b -@ b
a `seq` b = let 1 () = consume a in b

public export
interface Duplicable a where
  duplicate : (1 v : a) -> 2 `Copies` v

export
Duplicable Void where
  duplicate v impossible

export
Duplicable () where
  duplicate () = [(), ()]

export
Duplicable Bool where
  duplicate True  = [True, True]
  duplicate False = [False, False]

export
Duplicable (!* a) where
  duplicate (MkBang v) = [MkBang v, MkBang v]

||| Comonoid is the dual of Monoid, it can consume a value linearly and duplicate a value linearly
||| `comult` returns a pair instead of 2 copies, because we do not guarantee that the two values
||| are identical, unlike with `duplicate`. For example if we build a comonoid out of a group, with
||| comult returning both the element given and its inverse:
||| comult x = x # inverse x
||| It is not necessarily the case that x equals its inverse. For example the finite groupe of size
||| 3, has 1 and 2 as inverses of each other wrt to addition, but are not the same.
public export
interface Comonoid a where
  counit : a -@ ()
  comult : a -@ LPair a a

||| If a value is consumable and duplicable we can make an instance of Comonoid for it
export
[AutoComonoid] Consumable a => Duplicable a => Comonoid a where
  counit = consume
  comult x = pair (duplicate x)

export
Comonoid (!* a) where
  counit (MkBang _) = ()
  comult (MkBang v) = MkBang v # MkBang v
