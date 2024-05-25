
module Test

import Data.Vect

private typebind infixr 0 =@
private infixr 0 -@

%hide Prelude.Ops.infixl.(|>)

-- typebind infixr 1 =@@

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

-- map : (x : a) =@@ b -@ (y : List a) =@ List b

map2 : ((x : a) =@ b) -@ (y : List a) =@ List b

map3 : (x : a) =@ b -@ (y : List a) =@ List b

map4 : (x : a) =@ (b -@ (y : List a) =@ List b)

-- this could be possible if we allowed binding operators
-- with higher precedences
-- test : Test.map === Test.map2
-- failing
--   test2 : Test.map === Test.map3

test3 : Test.map3 === Test.map4

private typebind infixr 0 *>

-- (*>) : (ty : Type) -> (ty -> Type) -> Type
-- (*>) = DPair
--
-- testCompose : (x : Nat) *> (y : Nat) *> Vect (n + m) String
-- testCompose = (1 ** 2 ** ["hello", "world", "!"])

private autobind infixr 0 `MyLet`

MyLet : (val) -> (val -> rest) -> rest
MyLet arg fn = fn arg

program : Nat
program = (n := 3) `MyLet` 2 + n

program2 : Nat
program2 = (n : Nat := 3) `MyLet` 2 + n

private typebind infixr 0 |>

record Container where
  constructor (|>)
  shape : Type
  position : shape -> Type

private typebind infixr 0 @@

record (@@) (x : Type) (y : x -> Type) where
  constructor PairUp
  fst : x
  snd : y fst

compose : Container -> Container -> Container
compose (a |> a') (b |> b') =
  (x : (y : a) @@ (a' y -> b)) |>
       (y : a' x.fst) @@
            b' (x.snd y)
