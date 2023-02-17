||| Abstract binding trees are a generic representation of terms over
||| a given signature
module Language.IntrinsicTyping.ABT

import Data.SnocList.Elem

%default total

------------------------------------------------------------------------
-- The Type

parameters {0 kind : Type}

  ||| A constructor's argument describes the kind of the variables that
  ||| will be bound in the subterm as well as the overall type of the
  ||| argument.
  |||   The argument `n` in `S n`   is described by `MkArgument [] Nat`
  |||   The argument `b` in `\x. b` is described by `MkArgument [s] t`
  public export
  record Argument where
    constructor MkArgument
    binders : List kind
    argType : kind

  ||| A signature is a relation describing constructors.
  ||| Each constructor has a list of arguments and a return type.
  public export
  0 Signature : Type
  Signature = List Argument -> kind -> Type

  ||| Terms and Args are mutually defined.
  ||| A term is either a variable or a constructor fully applied to its arguments.
  data Term : (sig : Signature) -> (ctx : SnocList kind) -> kind -> Type

  ||| Terms and Args are mutually defined.
  ||| Arguments are an Arguments-indexed list of subterms.
  data Args : (sig : Signature) -> (ctx : SnocList kind) -> List Argument -> Type

  public export
  data Term : (sig : Signature) -> (ctx : SnocList kind) -> kind -> Type where
    ||| Variables are represented using typed De Bruijn indices.
    Var : Elem s ctx -> Term sig ctx s
    ||| Constructors are provided by the signature
    Con : sig args s -> Args sig ctx args -> Term sig ctx s

  public export
  data Args : (sig : Signature) -> (ctx : SnocList kind) -> List Argument -> Type where
    ||| Empty list
    Nil  : Args sig ctx []
    ||| An argument with binders `bds` and return type `s` is provided by a term
    ||| whose scope has been extended by `bds` and whose return type is `s`.
    (::) : {bds : List kind} ->
           Term sig (ctx <>< bds) s ->
           Args sig ctx args ->
           Args sig ctx (MkArgument bds s :: args)

------------------------------------------------------------------------
-- An example: STLC + Nat

namespace Example

  ||| The natural numbers & arrow types
  data TY = NAT | ARR TY TY

  ||| A signature for STLC with natural numbers
  data SIG : Signature {kind = TY} where
    ||| Zero takes no argument
    ||| and returns a NAT
    Z : SIG [] NAT
    ||| Succ takes one argument (of type NAT, with no extra variable in scope),
    ||| and returns a NAT
    S : SIG [MkArgument [] NAT] NAT
    ||| Lam takes one argument (of type t, with an extra variable of type s in scope),
    ||| and returns a function from s to t
    LAM : SIG [MkArgument [s] t] (ARR s t)
    ||| App takes two arguments (of type (Arr s t) and s respectively,
    ||| with no extra variable in scope for either), and returns a t
    APP : SIG [MkArgument [] (ARR s t), MkArgument [] s] t

  ||| Pattern synonym for Zero
  Zero : Term SIG ctx NAT
  Zero = Con Z []

  ||| Pattern synonym for Succ
  Succ : Term SIG ctx NAT -> Term SIG ctx NAT
  Succ n = Con S [n]

  ||| Pattern synonym for Lam
  Lam : {s : TY} -> Term SIG (ctx :< s) t -> Term SIG ctx (ARR s t)
  Lam b = Con LAM [b]

  ||| Pattern synonym for App
  App : Term SIG ctx (ARR s t) -> Term SIG ctx s -> Term SIG ctx t
  App f t = Con APP [f, t]

------------------------------------------------------------------------
-- Generic renaming

public export
lift : (forall s. Elem s ctx -> Elem s ctx') ->
       (forall s. Elem s (ctx :< t) -> Elem s (ctx' :< t))
lift f Here = Here
lift f (There v) = There (f v)

public export
lifts : (bds : List kind) ->
        (forall s. Elem s ctx -> Elem s ctx') ->
        (forall s. Elem s (ctx <>< bds) -> Elem s (ctx' <>< bds))
lifts [] f = f
lifts (s :: ss) f = lifts ss (lift f)

public export
rename : (forall s. Elem s ctx -> Elem s ctx') ->
         (forall s. Term sig ctx s -> Term sig ctx' s)

public export
renames : (forall s. Elem s ctx -> Elem s ctx') ->
          (forall args. Args sig ctx args -> Args sig ctx' args)

rename f (Var v) = Var (f v)
rename f (Con c args) = Con c (renames f args)

renames f [] = []
renames f (arg :: args) = rename (lifts _ f) arg :: renames f args

------------------------------------------------------------------------
-- Generic substitution

public export
extend : (forall s. Elem s ctx -> Term sig ctx' s) ->
         (forall s. Elem s (ctx :< t) -> Term sig (ctx' :< t) s)
extend f Here = Var Here
extend f (There v) = rename There (f v)

public export
extends : (bds : List kind) ->
          (forall s. Elem s ctx -> Term sig ctx' s) ->
          (forall s. Elem s (ctx <>< bds) -> Term sig (ctx' <>< bds) s)
extends [] f = f
extends (s :: ss) f = extends ss (extend f)

public export
substitute : (forall s. Elem s ctx -> Term sig ctx' s) ->
             (forall s. Term sig ctx s -> Term sig ctx' s)

public export
substitutes : (forall s. Elem s ctx -> Term sig ctx' s) ->
              (forall args. Args sig ctx args -> Args sig ctx' args)

substitute f (Var v) = f v
substitute f (Con c args) = Con c (substitutes f args)

substitutes f [] = []
substitutes f (arg :: args) = substitute (extends _ f) arg :: substitutes f args
