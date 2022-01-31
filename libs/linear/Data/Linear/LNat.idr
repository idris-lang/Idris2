module Data.Linear.LNat

import Data.Linear.Bifunctor
import Data.Linear.Copies
import Data.Linear.Notation

||| Linear Nat
public export
data LNat : Type where
  Zero : LNat
  Succ : LNat -@ LNat

||| Convert a linear nat to an unrestricted Nat, only usable at the type level
||| because we canot call `S` with an argument that is expected to be used exactly once
public export
0 toNat : LNat -@ Nat
toNat Zero = Z
toNat (Succ n) = S (toNat n)

export
Consumable LNat where
  consume Zero = ()
  consume (Succ n) = consume n

export
Duplicate LNat where
  dup Zero = Zero # Zero
  dup (Succ n) = bimap Succ Succ (Notation.dup n)

||| Add two linear numbers
export
add : LNat -@ LNat -@ LNat
add Zero x = x
add (Succ v) x = Succ (add v x)

||| Multiply two linear numbers
export
mult : (1 n : LNat) -> (0 l : LNat) -> {auto 1 ls : toNat n `Copies` l} -> LNat
mult Zero x {ls = []} = Zero
mult (Succ v) x {ls = x :: ls} = add x (mult {ls} v x)

||| Square a linear number
export
square : (1 v : LNat) -> {auto 1 vs : toNat v `Copies` v} -> LNat
square v {vs} = mult {ls = vs} v v
