
module Test

import Data.Vect

typebind infixr 0 =@
infixr 0 -@

typebind infix 1 =@@

0 (=@) : (a : Type) -> (a -> Type) -> Type
(=@) a f = (1 x : a) -> f x

0 (=@@) : (a : Type) -> (a -> Type) -> Type
(=@@) a f = (1 x : a) -> f x

(-@) : (a, b : Type) -> Type
(-@) a b = (1 _ : a) -> b

data S : {ty : Type} -> (x : ty) -> Type where
  MkS : (x : ty) =@ S x
  Mk2 : (x : ty) =@ (y : ty) =@ S (x, y)
  Mk3 : (x : ty) =@ ty -@ S x
  Mk4 : ty -@ (x : ty) =@ S x

map : (x : a) =@@ b -@ (y : List a) =@ List b

map2 : ((x : a) =@ b) -@ (y : List a) =@ List b

map3 : (x : a) =@ b -@ (y : List a) =@ List b

map4 : (x : a) =@ (b -@ (y : List a) =@ List b)

test : Test.map === Test.map2

failing
  test2 : Test.map === Test.map3

test3 : Test.map3 === Test.map4

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
