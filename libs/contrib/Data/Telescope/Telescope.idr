||| The telescope data structures.
|||
||| Indexing telescopes by their length (hopefully) helps inform the
||| type-checker during inference.
module Data.Telescope.Telescope

import Data.DPair
import Data.Nat
import Data.Fin

%default total

public export
plusAcc : Nat -> Nat -> Nat
plusAcc Z n = n
plusAcc (S m) n = plusAcc m (S n)

export
plusAccIsPlus : (m, n : Nat) -> (m + n) === plusAcc m n
plusAccIsPlus Z n = Refl
plusAccIsPlus (S m) n =
  rewrite plusSuccRightSucc m n in
  plusAccIsPlus m (S n)

public export
plusAccZeroRightNeutral : (m : Nat) -> plusAcc m 0 === m
plusAccZeroRightNeutral m =
  rewrite sym (plusAccIsPlus m 0) in
  rewrite plusZeroRightNeutral m in
  Refl


infixl 4 -.
infixr 4 .-

namespace Left

  mutual
    ||| A left-nested sequence of dependent types
    public export
    data Telescope : (k : Nat) -> Type where
      Nil  : Telescope 0
      (-.) : (gamma : Left.Telescope k) -> (ty : TypeIn gamma) -> Telescope (S k)

    ||| A type with dependencies in the given context
    public export
    TypeIn : Left.Telescope k -> Type
    TypeIn gamma = (env : Environment gamma) -> Type

    ||| A tuple of values of each type in the telescope
    public export
    Environment : Left.Telescope k -> Type
    Environment [] = ()
    Environment (gamma -. ty) = (env : Environment gamma ** ty env)

  export
  weakenTypeIn : TypeIn gamma -> TypeIn (gamma -. sigma)
  weakenTypeIn ty env = ty (fst env)

  public export
  uncons : (gamma : Telescope (S k)) ->
           (ty : Type
            ** delta : (ty -> Telescope k)
            ** (v : ty) -> Environment (delta v) -> Environment gamma)
  uncons ([] -. ty) = (ty () ** const [] ** \ v, _ => (() ** v))
  uncons (gamma@(_ -. _) -. ty) =
    let (sigma ** delta ** left) = uncons gamma in
    (sigma ** (\ v => delta v -. (\ env => ty (left v env)))
           ** (\ v, (env ** w) => (left v env ** w)))

  public export
  (++) : {n : Nat} -> (gamma : Left.Telescope m) -> (Environment gamma -> Left.Telescope n) ->
         Telescope (plusAcc n m)
  (++) {n = Z} gamma delta = gamma
  (++) {n = S n} gamma delta = (gamma -. sigma) ++ uncurry theta where

    sigma : Environment gamma -> Type
    sigma env = fst (uncons (delta env))

    theta : (env : Environment gamma) -> sigma env -> Telescope n
    theta env val with (uncons (delta env))
      theta env val | (sig ** omega ** _) = omega val

  public export
  cons : {k : Nat} -> (ty : Type) -> (ty -> Left.Telescope k) -> Left.Telescope (S k)
  cons sigma gamma =
    rewrite plusCommutative 1 k in
    rewrite plusAccIsPlus k 1 in
    ([] -. const sigma) ++ (gamma . snd)

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

namespace Right

  mutual
    ||| A right-nested sequence of dependent types
    public export
    data Telescope : (k : Nat) -> Type where
      Nil  : Telescope 0
      (.-) : (ty : Type) -> (gamma : ty -> Right.Telescope k) -> Telescope (S k)

    ||| A tuple of values of each type in the telescope
    public export
    Environment : Right.Telescope k -> Type
    Environment [] = ()
    Environment (ty .- gamma) = (v : ty ** Environment (gamma v))

  export
  empty : (0 gamma : Right.Telescope Z) -> Environment gamma
  empty {gamma = []} = ()

  export
  snoc : (gamma : Right.Telescope k) -> (Environment gamma -> Type) -> Right.Telescope (S k)
  snoc [] tau   = tau () .- const []
  snoc (sigma .- gamma) tau = sigma .- \ v => snoc (gamma v) (\ env => tau (v ** env))

  export
  unsnoc : {k : Nat} -> (gamma : Right.Telescope (S k)) ->
           (delta : Right.Telescope k
            ** sigma : (Environment delta -> Type)
            ** (env : Environment delta) -> sigma env -> Environment gamma)
  unsnoc {k = Z} (sigma .- gamma) = ([] ** const sigma ** \ (), v => (v ** empty (gamma v)))
  unsnoc {k = S k} (sigma .- gamma)
    = (sigma .- delta ** uncurry tau ** \ (v ** env) => transp v env) where

    delta : sigma -> Right.Telescope k
    delta v = fst (unsnoc (gamma v))

    tau : (v : sigma) -> Environment (delta v) -> Type
    tau v = fst (snd (unsnoc (gamma v)))

    transp : (v : sigma) -> (env : Environment (delta v)) -> tau v env -> Environment (sigma .- gamma)
    transp v env w = (v ** (snd (snd (unsnoc (gamma v))) env w))

  export
  (++) : (gamma : Right.Telescope m) -> (Environment gamma -> Right.Telescope n) -> Right.Telescope (m + n)
  [] ++ delta = delta ()
  (sigma .- gamma) ++ delta = sigma .- (\ v => (gamma v ++ (\ env => delta (v ** env))))

  export
  split : (gamma : Right.Telescope m) -> (delta : Environment gamma -> Right.Telescope n) ->
          Environment (gamma ++ delta) ->
          (env : Environment gamma ** Environment (delta env))
  split [] delta env = (() ** env)
  split (sigma .- gamma) delta (v ** env) =
    let (env1 ** env2) = split (gamma v) (\env => delta (v ** env)) env in
    ((v ** env1) ** env2)

namespace Tree

  infixl 4 ++

  mutual
    ||| A tree of dependent types
    public export
    data Telescope : (k : Nat) -> Type where
      Nil  : Telescope 0
      Elt  : Type -> Telescope 1
      (++) : (gamma : Tree.Telescope m) ->
             (delta : Tree.Environment gamma -> Tree.Telescope n) ->
              Telescope (m + n)

    ||| A tuple of values of each type in the telescope
    public export
    Environment : Tree.Telescope k -> Type
    Environment [] = ()
    Environment (Elt t) = t
    Environment (gamma ++ delta) = (env : Environment gamma ** Environment (delta env))

  export
  concat : (gamma : Tree.Telescope k) -> (delta : Right.Telescope k ** Environment delta -> Environment gamma)
  concat Nil = ([] ** id)
  concat (Elt t) = ((t .- const []) ** fst)
  concat (gamma ++ delta) =
    let (thetaL ** transpL) = concat gamma in
    ((thetaL ++ \ envL => fst (concat (delta (transpL envL))))
    ** \ env =>
         let (env1 ** env2) = split thetaL (\ envL => fst (concat (delta (transpL envL)))) env in
         (transpL env1 ** snd (concat (delta (transpL env1))) env2)
    )

infix 5 <++>

public export
(<++>) : (gamma : Left.Telescope m) -> (Environment gamma -> Right.Telescope n) -> Right.Telescope (plusAcc m n)
[] <++> delta = delta ()
(gamma -. sigma ) <++> delta = gamma <++> (\ env => sigma env .- \ v => delta (env ** v))

infix 5 >++<

(>++<) : {m, n : Nat} -> (gamma : Right.Telescope m) -> (Environment gamma -> Left.Telescope n) ->
         Left.Telescope (plusAcc m n)
[] >++< delta = delta ()
gamma@(_ .- _) >++< delta =
  let (gamma ** sigma ** transp) = unsnoc gamma in
  gamma >++< \ env => (cons (sigma env) (\ v => delta (transp env v)))

export
leftToRight : Left.Telescope m -> Right.Telescope m
leftToRight gamma = rewrite sym (plusAccZeroRightNeutral m) in (gamma <++> const [])

export
rightToLeft : {m : Nat} -> Right.Telescope m -> Left.Telescope m
rightToLeft gamma = rewrite sym (plusAccZeroRightNeutral m) in (gamma >++< const [])
