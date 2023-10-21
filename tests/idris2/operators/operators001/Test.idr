

import Data.Vect

typebind infixr 0 =@

0 (=@) : (a : Type) -> (a -> Type) -> Type
(=@) a f = (1 x : a) -> f x


data S : {ty : Type} -> (x : ty) -> Type where
  MkS : (x : ty) =@ S x

typebind infixr 0 *>

-- (*>) : (ty : Type) -> (ty -> Type) -> Type
-- (*>) = DPair
--
-- testCompose : (x : Nat) *> (y : Nat) *> Vect (n + m) String
-- testCompose = (1 ** 2 ** ["hello", "world", "!"])

autobind infixr 7 `MyLet`

MyLet : (val) -> (val -> rest) -> rest
MyLet arg fn = fn arg

program : Nat
program = (n := 3) `MyLet` 2 + n

program2 : Nat
program2 = (n : Nat := 3) `MyLet` 2 + n
