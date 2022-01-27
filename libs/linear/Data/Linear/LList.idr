module Data.Linear.LList

import Data.Linear.Notation
import Data.Linear.LNat

public export
data LList : Type -> Type where
  Nil : LList a
  (::) : a -@ LList a -@ LList a

%name LList xs, ys, zs, ws

export
length : (c : Consumable a) => LList a -@ LNat
length [] = Zero
length (x :: xs) = let () = consume x in
                    Succ (Linear.LList.length @{c} xs)
