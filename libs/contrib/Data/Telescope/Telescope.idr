||| The telescope data structure.
|||
||| Indexing telescopes by their length (hopefully) helps inform the
||| type-checker during inference.
module Data.Telescope.Telescope

import Data.DPair
import Data.Nat
import Data.Fin
import Syntax.PreorderReasoning

%default total

infixl 4 -.,=.
prefix 3 -|

mutual
  ||| A left-nested sequence of dependent types
  public export
  data Telescope : (k : Nat) -> Type where
    Nil  : Telescope 0
    (-.) : (gamma : Telescope k) -> (ty : TypeIn gamma) -> Telescope (S k)

  ||| A type with dependencies in the given context
  public export
  TypeIn : Telescope k -> Type
  TypeIn gamma = (env : Environment gamma) -> Type

  ||| A tuple of values of each type in the telescope
  public export
  Environment : Telescope k -> Type
  Environment [] = ()
  Environment (gamma -. ty) = (env : Environment gamma ** ty env)

%name Telescope   gamma,gamma',gamma1,gamma2,gamma3
%name Environment env,env',env1,env2,env3
%name TypeIn ty,ty',ty1,ty2,ty3

public export
weakenTypeIn : TypeIn gamma -> TypeIn (gamma -. ty)
weakenTypeIn ty' (env ** _) = ty' env

public export
uncons : (gamma : Telescope (S k)) ->
         (ty : Type ** delta : (ty -> Telescope k)
          ** (v : ty) -> Environment (delta v) -> Environment gamma)
uncons ([] -. ty) = (ty () ** const [] ** \ v, _ => (() ** v))
uncons (gamma@(_ -. _) -. ty) =
  let (sigma ** delta ** left) = uncons gamma in
  (sigma ** (\ v => delta v -. (\ env => ty (left v env)))
         ** (\ v, (env ** w) => (left v env ** w)))

public export
plusAcc : Nat -> Nat -> Nat
plusAcc Z n = n
plusAcc (S m) n = plusAcc m (S n)

export
plusAccIsPlus : (m, n : Nat) -> plusAcc m n === (m + n)
plusAccIsPlus Z n = Refl
plusAccIsPlus (S m) n =
  rewrite plusSuccRightSucc m n in
  plusAccIsPlus m (S n)

public export
(++) : {n : Nat} -> (gamma : Telescope m) -> (Environment gamma -> Telescope n) -> Telescope (plusAcc n m)
(++) {n = Z} gamma delta = gamma
(++) {m} {n = S n} gamma delta = (gamma -. sigma) ++ uncurry theta where

  sigma : Environment gamma -> Type
  sigma env = fst (uncons (delta env))

  theta : (env : Environment gamma) -> sigma env -> Telescope n
  theta env val with (uncons (delta env))
    theta env val | (sig ** omega ** _) = omega val

public export
cons : {n : Nat} -> (ty : Type) -> (ty -> Telescope n) -> Telescope (S n)
cons {n} ty gamma =
  rewrite plusCommutative 1 n in
  rewrite sym (plusAccIsPlus n 1) in
  ([] -. const ty) ++ (gamma . snd)

||| A position between the variables of a telescope, counting from the _end_:
||| Telescope:   Nil -. ty1 -. ... -. tyn
||| Positions: ^k    ^k-1   ^k-2   ^1     ^0
public export
Position : {k : Nat} -> Telescope k -> Type
Position {k} _ = Fin (S k)

||| The position at the beginning of the telescope
public export
start : {k : Nat} -> (gamma : Telescope k) -> Position gamma
start {k} gamma = last
