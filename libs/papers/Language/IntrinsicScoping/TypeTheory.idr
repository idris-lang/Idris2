||| The content of this module is based on the paper:
||| A tutorial implementation of a dependently typed lambda calculus
||| by Andres Löh, Conor McBride, and Wouter Swierstra
|||
||| NB: Unlike `Language.TypeTheory`, this is not a direct translation
|||     of the code in the paper but rather a more idiomatic solution.
module Language.IntrinsicScoping.TypeTheory

import Control.Monad.Error.Interface
import Decidable.Equality
import Data.SnocList
import Data.List.Quantifiers
import Data.SnocList.Quantifiers

import Language.IntrinsicScoping.Variables

-- We go straight to Section 4: LambdaPi + natural numbers

------------------------------------------------------------------------
-- Syntax
-- This tutorial uses a locally-nameless presentation.
-- In the intrinsically scoped world, this means that everything is doubly
-- indexed here. Each term has:
--
-- * an LContext of variables using De Bruijn *L*evels.
--   It is used for free variables, the level do not change when we push
--   the term under a new binder
--
-- * an IContext of variables using De Bruijn *I*ndices.
--   It is used for bound variables, the indices pointing to free variables
--   would change when we push the term under a new binder.
--
-- Every time we go under a binder, the corresponding index is turned
-- into level. This ensures we only ever manipulate terms whose free
-- variables are levels and so can be weakened "for free".
------------------------------------------------------------------------

public export
Scoped : Type
Scoped = LContext -> IContext -> Type

||| Abs binds the most local variable
data Abs : Scoped -> Scoped where
  MkAbs : (x : Name) -> t f (g :< x) -> Abs t f g

||| Infer-able terms are those whose type can be reconstructed
data Infer : Scoped

||| Check-able terms are those whose type can be checked
data Check : Scoped

total
data Infer : Scoped where
  ||| A checkable term annotated with its expected type
  Ann : (t, ty : Check f g) -> Infer f g
  ||| The star kind is inferrable
  Star : Infer f g
  ||| The nat type is inferrable
  Nat : Infer f g
  ||| The nat induction principle is inferrable
  Rec : (pred, pz, ps : Check f g) -> (n : Check f g) -> Infer f g

  -- This is fairly unconventional: in order to support overloaded
  -- data constructors disambiguated in a type-direct manner, we would
  -- typically put zero, suc, & friends in `Check`.
  ||| The zero constructor is inferrable
  Zro : Infer f g
  ||| The successor constructor is inferrable
  Suc : Check f g -> Infer f g
  ||| Pi is inferrable
  Pi : (a : Check f g) -> (b : Abs Check f g) -> Infer f g
  ||| A bound variable
  Bnd : Index nm g -> Infer f g
  ||| A free variable
  Var : Level nm f -> Infer f g
  ||| The application of a function to its argument
  App : Infer f g -> Check f g -> Infer f g

export infixl 3 `App`

%name Infer e

total
data Check : Scoped where
  ||| Inferrable terms are trivially checkable
  Emb : Infer f g -> Check f g
  ||| A function binding its argument
  Lam : Abs Check f g -> Check f g

%name Check s, t

------------------------------------------------------------------------
-- Free operations (thanks to indices & level properties)

namespace Check
  -- here it's okay to use believe_me precisely because embedding
  -- terms in a wider LContext does not change any of their syntax
  export
  thin : (0 ext : _) -> Check f g -> Check (ext ++ f) g
  thin ext = believe_me

namespace Infer
  -- here it's okay to use believe_me precisely because embedding
  -- terms in a wider LContext does not change any of their syntax
  export
  thin : (0 ext : _) -> Infer f g -> Infer (ext ++ f) g
  thin ext = believe_me

  -- here it's okay to use believe_me because there are no bound
  -- variables
  export
  closed : (0 g : _) -> Infer f [<] -> Infer f g
  closed g = believe_me

------------------------------------------------------------------------
-- Equality testing

(forall g. Eq (t f g)) => Eq (Abs t f g) where
  MkAbs x@_ b == MkAbs x' b' with (decEq x x')
    _ | Yes Refl = b == b'
    _ | No _ = False

Eq (Infer f g)
Eq (Check f g)

Eq (Infer f g) where
  Ann t ty == Ann t' ty' = t == t' && ty == ty'
  Star == Star = True
  Pi a b == Pi s t = a == s && b == t
  Bnd k == Bnd l = case hetEqDec k l of
    Yes _ => True
    _ => False
  Var m == Var n = case hetEqDec m n of
    Yes _ => True
    _ => False
  App e s == App f t = e == f && s == t
  _ == _ = False

Eq (Check f g) where
  Emb e == Emb f = assert_total (e == f)
  Lam b == Lam t = assert_total (b == t)
  _ == _ = False

------------------------------------------------------------------------
-- Substituting a closed term for the outermost de Bruijn index
--
-- This will allow us to open a closed `Abs` by converting the most local
-- de Bruijn index into a fresh de Bruijn level.

parameters {0 x : Name}

  substAbs   : {g : _} -> Infer f [<] -> Abs Check f ([<x] <+> g) -> Abs Check f g
  substCheck : {g : _} -> Infer f [<] -> Check f ([<x] <+> g) -> Check f g
  substInfer : {g : _} -> Infer f [<] -> Infer f ([<x] <+> g)  -> Infer f g

  substCheck u (Emb t) = Emb (substInfer u t)
  substCheck u (Lam b) = Lam (substAbs u b)

  substInfer u (Ann s a) = Ann (substCheck u s) (substCheck u a)
  substInfer u Star = Star
  substInfer u Nat = Nat
  substInfer u Zro = Zro
  substInfer u (Suc n) = Suc (substCheck u n)
  substInfer u (Rec p pz ps n)
    = Rec (substCheck u p) (substCheck u pz) (substCheck u ps) (substCheck u n)
  substInfer u (Pi a b) = Pi (substCheck u a) (substAbs u b)
  substInfer {g} u (Bnd k) = case isLast k of
    Left _ => closed g u
    Right k' => Bnd k'
  substInfer u (Var nm) = Var nm
  substInfer u (App e s) = App (substInfer u e) (substCheck u s)

  substAbs u (MkAbs y t) = MkAbs y (substCheck u t)

------------------------------------------------------------------------
-- Semantics
--
-- Values only use de Bruijn levels. The syntax's binders are interpreted
-- as functions in the host language, and so the de Bruijn indices have
-- become variables in the host language.
------------------------------------------------------------------------

||| Function are interpreted using a Kripke function space:
||| we know how to run the function in any extended context.
0 Kripke : LContext -> Type

data Value : LContext -> Type
data Stuck : LContext -> Type

data Value : LContext -> Type where
  ||| Lambda abstractions become functions in the host language
  VLam  : (b : Kripke f) -> Value f
  ||| The Star kind is a value already
  VStar : Value f
  ||| The nat type is a value already
  VNat : Value f
  ||| The zero constructor is a value
  VZro : Value f
  ||| The successor constructor is a value constructor
  VSuc : Value f -> Value f
  ||| Pi constructors combine a value for their domain and
  ||| a function in the host language for their codomain
  VPi   : (a : Value f) -> (b : Kripke f) -> Value f
  ||| Stuck computations qualify as values
  VEmb  : (e : Stuck f) -> Value f

data Stuck : LContext -> Type where
  ||| A variable is a stuck computation
  NVar : Level nm f -> Stuck f
  ||| An application whose function is stuck is also stuck
  NApp : Stuck f -> Value f -> Stuck f
  ||| An induction principle applied to a stuck natural numnber is stuck
  NRec : (pred, pz, ps : Value f) -> Stuck f -> Stuck f

Kripke f = (0 ext : _) -> Value (ext ++ f) -> Value (ext ++ f)

namespace Value
  -- here it's okay to use believe_me precisely because embedding
  -- terms in a wider LContext does not change any of their syntax
  export
  thin : (0 ext : _) -> Value f -> Value (ext ++ f)
  thin ext = believe_me

------------------------------------------------------------------------
-- Evaluation

||| We can easily turn a level into a value
||| by building a stuck computation first
vfree : Level nm f -> Value f
vfree x = VEmb (NVar x)

export infixl 5 `vapp`

||| We can easily apply a value standing for a function
||| to a value standing for its argument by either deploying
||| the function or growing the spine of the stuck computation.
partial
vapp : Value f -> Value f -> Value f
vapp (VLam f) t = f [] t
vapp (VEmb n) t = VEmb (NApp n t)
vapp _ _ = idris_crash "INTERNAL ERROR: vapp -> impossible case"

||| An environment is a list of values for all the bound variables in scope
Env : Scoped
Env f g = All (const (Value f)) g

||| Indices are mapped to environment values
evalIndex : Index nm g -> Env f g -> Value f
evalIndex i@_ env with (view i)
  evalIndex i@_ (_ :< v) | Z = v
  evalIndex i@_ (env :< _) | S i' = evalIndex i' env

||| Big step evaluation of an inferrable term in a given environment
partial
evalInfer : Infer f g -> Env f g -> Value f

||| Big step evaluation of a checkable term in a given environment
partial
evalCheck : Check f g -> Env f g -> Value f

partial
evalAbs : Abs Check f g -> Env f g -> Kripke f

evalInfer (Ann t _) env = evalCheck t env
evalInfer Star env = VStar
evalInfer Nat env = VNat
evalInfer Zro env = VZro
evalInfer (Suc n) env = VSuc (evalCheck n env)
evalInfer (Rec p pz ps n) env = go (evalCheck pz env) (evalCheck ps env) (evalCheck n env) where

  go : (pz, ps, n : Value f) -> Value f
  go pz ps VZro = pz
  go pz ps (VSuc n) = ps `vapp` n `vapp` (go pz ps n)
  go pz ps (VEmb n) = VEmb (NRec (evalCheck p env) pz ps n)
  go _ _ _ = idris_crash "INTERNAL ERROR: evalInfer -> impossible case"

evalInfer (Pi a b) env = VPi (evalCheck a env) (evalAbs b env)
evalInfer (Bnd i) env = evalIndex i env
evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

evalCheck (Emb i) env = evalInfer i env
evalCheck (Lam b) env = VLam (evalAbs b env)

evalAbs {f} (MkAbs x b) env
  -- here it's okay to use believe_me precisely because embedding
  -- terms in a wider LContext does not change any of their syntax
  = \ ext, v => evalCheck {f = ext ++ f, g = g :< x} (believe_me b) (believe_me env :< v)


------------------------------------------------------------------------
-- Reification

quoteStuckI : {f : _} -> Stuck f -> Infer [] (rev f)
quoteAbsI   : {f : _} -> Kripke f -> Abs Check [] (rev f)
quoteValueI : {f : _} -> Value f -> Check [] (rev f)

quoteStuckI (NVar v) = Bnd (asIndex v)
quoteStuckI (NApp e t) = quoteStuckI e `App` quoteValueI t
quoteStuckI (NRec pred pz ps e)
  = Rec (quoteValueI pred) (quoteValueI pz) (quoteValueI ps) (Emb (quoteStuckI e))

quoteValueI VStar = Emb Star
quoteValueI VNat = Emb Nat
quoteValueI VZro = Emb Zro
quoteValueI (VSuc n) = Emb (Suc (quoteValueI n))
quoteValueI (VPi a b)
  = let a = quoteValueI a in
    let b = quoteAbsI b in
    Emb (Pi a b)
quoteValueI (VLam f) = Lam (quoteAbsI f)
quoteValueI (VEmb e) = Emb (quoteStuckI e)

quoteAbsI {f} b
  = let nm = fromString "x_\{show (length f)}" in
    MkAbs nm (quoteValueI (b [nm] (vfree fresh)))

quoteValue : {f : _} -> Value f -> Check [] (rev f)
quoteValue = quoteValueI

------------------------------------------------------------------------
-- Normalisation is evaluation followed by reification

partial
normCheck : Check [] g -> Env [] g  -> Check [] [<]
normCheck t env = quoteValue (evalCheck t env)

partial
normInfer : Infer [] g -> Env [] g -> Check [] [<]
normInfer t env = quoteValue (evalInfer t env)

------------------------------------------------------------------------
-- Typechecking
--
-- Note that here we keep the terms closed by turning de Bruijn indices
-- into de Bruijn levels (cf. checkAbsI).
------------------------------------------------------------------------

||| Types are just values in TT
Ty : LContext -> Type
Ty = Value

||| A context maps names to types, that is to say values
Context : LContext -> Type
Context f = All (const (Ty f)) f

parameters {0 m : Type -> Type} {auto _ : MonadError String m}

  levelI : {f : _} -> All (const p) f -> Level nm f -> p
  levelI vs lvl with (view lvl)
    levelI (v :: vs) _ | Z = v
    levelI (v :: vs) _ | S lvl' = levelI vs lvl'

  inferI    : {f : _} -> Context f -> Infer f [<] -> m (Ty f)
  checkAbsI : {f : _} -> Context f -> Ty f -> Kripke f -> Abs Check f [<] -> m ()
  checkI    : {f : _} -> Context f -> Ty f -> Check f [<] -> m ()

  inferI ctx (Ann t ty) = do
    checkI ctx VStar ty
    let ty = assert_total (evalCheck ty [<])
    ty <$ checkI ctx ty t
  inferI ctx Star = pure VStar
  inferI ctx Nat = pure VStar
  inferI ctx Zro = pure VNat
  inferI ctx (Suc n) = VNat <$ checkI ctx VNat n
  inferI ctx (Rec p pz ps n) = do
    -- check & evaluate the predicate
    checkI ctx (VPi VNat (\ _, _ => VStar)) p
    let p = assert_total (evalCheck p [<])
    -- check pz has type (p 0)
    checkI ctx (assert_total (p `vapp` VZro)) pz
    -- check ps has type (forall n. p n -> p (1+ n))
    let psTy = VPi VNat $ \ ext, n =>
               VPi (thin ext p `vapp` n) $
               \ ext', _ => thin ext' (thin ext p `vapp` VSuc n)
    checkI ctx psTy ps
    -- check & evaluate the nat
    checkI ctx VNat n
    let n = assert_total (evalCheck n [<])
    -- return (p n)
    pure (assert_total (p `vapp` n))
  inferI ctx (Pi a b) = do
    checkI ctx VStar a
    let a = assert_total (evalCheck a [<])
    VStar <$ checkAbsI ctx a (\ _, _ => VStar) b
  inferI ctx (Bnd k) =
    -- unhandled in the original Haskell
    throwError "Oops"
  inferI ctx (Var v) = pure (levelI ctx v)
  inferI ctx (App f t) = do
    (VPi a b) <- inferI ctx f
      | _ => throwError "illegal application"
    checkI ctx a t
    let t = assert_total (evalCheck t [<])
    pure (b [] t)


  checkI ctx ty (Emb t) = do
    ty' <- inferI ctx t
    unless (quoteValue ty == quoteValue ty') $ throwError "type mismatch"
  checkI ctx ty (Lam t) = do
    let VPi a b = ty
      | _ => throwError "expected a function type"
    checkAbsI ctx a b t

  checkAbsI {f} ctx a b (MkAbs x t) = do
    let b = b [x] (vfree fresh)
    -- Here we turn the most local de Bruijn index into a level
    let t = substCheck (Var fresh) (thin [x] t)
    checkI (thin [x] a :: believe_me ctx) b t
