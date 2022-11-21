||| The content of this module is based on the paper:
||| A tutorial implementation of a dependently typed lambda calculus
||| by Andres Löh, Conor McBride, and Wouter Swierstra
|||
||| NB: The work is originally written in Haskell and uses unsafe features
|||     This is not how we would write idiomatic Idris code.
|||     Cf. Core.TT's Term datatype for a more idiomatic implementation
module Language.TypeTheory

import Control.Monad.Error.Interface
import Data.List

%default covering

||| Section 2: Simply Typed Lambda Calculus
namespace Section2

  -- 2.4: Implementation

  ||| Named variables
  public export
  total
  data Name : Type where
    ||| The most typical of name: external functions
    Global : String -> Name
    ||| When passing under a binder we convert a bound variable
    ||| into a `Local` free variable
    Local : Nat -> Name
    ||| During quoting from values back to term we will be using
    ||| the `Quote` constructor
    Quote : Nat -> Name

  %name Name nm

  public export
  Eq Name where
    Global m == Global n = m == n
    Local m == Local n = m == n
    Quote m == Quote n = m == n
    _ == _ = False

  infixr 0 ~>
  total
  data Ty : Type where
    ||| A family of base types
    Base : Name -> Ty
    ||| A function type from
    ||| @i the type of the function's input to
    ||| @o the type of the function's output
    (~>) : (i, o : Ty) -> Ty

  %name Ty a, b

  Eq Ty where
    Base m == Base n = m == n
    (i ~> o) == (a ~> b) = i == a && o == b
    _ == _ = False

  -- Raw terms are neither scopechecked nor typecked

  ||| Inferable terms know what their type is
  data Infer : Type

  ||| Checkable terms need to be checked against a type
  data Check : Type

  total
  data Infer : Type where
    ||| A checkable term annotated with its expected type
    Ann : Check -> Ty -> Infer
    ||| A bound variable
    Bnd : Nat -> Infer
    ||| A free variable
    Var : Name -> Infer
    ||| The application of a function to its argument
    App : Infer -> Check -> Infer

  infixl 3 `App`

  %name Infer e, f

  total
  data Check : Type where
    ||| Inferable terms are trivially checkable
    Emb : Infer -> Check
    ||| A function binding its argument
    Lam : Check -> Check

  substCheck : Nat -> Infer -> Check -> Check
  substInfer : Nat -> Infer -> Infer -> Infer

  substCheck lvl u (Emb t) = Emb (substInfer lvl u t)
  substCheck lvl u (Lam b) = Lam (substCheck (S lvl) u b)

  substInfer lvl u (Ann s a) = Ann (substCheck lvl u s) a
  substInfer lvl u (Bnd k) = ifThenElse (lvl == k) u (Bnd k)
  substInfer lvl u (Var nm) = Var nm
  substInfer lvl u (App e s) = App (substInfer lvl u e) (substCheck lvl u s)

  %name Check s, t

  data Value : Type
  data Stuck : Type

  ||| Unsafe type of values
  data Value : Type where
    ||| Lambda abstractions become functions in the host language
    VLam : (Value -> Value) -> Value
    ||| Stuck computations qualify as values
    VEmb : Stuck -> Value

  ||| Type of stuck computations
  data Stuck : Type where
    ||| A variable is a stuck computation
    NVar : Name -> Stuck
    ||| An application whose function is stuck is also stuck
    NApp : Stuck -> Value -> Stuck

  ||| We can easily turn a name into a value
  ||| by building a stuck computation first
  vfree : Name -> Value
  vfree x = VEmb (NVar x)

  ||| We can easily apply a value standing for a function
  ||| to a value standing for its argument by either deploying
  ||| the function or growing the spine of the stuck computation.
  vapp : Value -> Value -> Value
  vapp (VLam f) t = f t
  vapp (VEmb n) t = VEmb (NApp n t)

  ||| An environment is a list of values for all the bound variables in scope
  Env : Type
  Env = List Value

  ||| Big step evaluation of an inferrable term in a given environment
  partial
  evalInfer : Infer -> Env -> Value

  ||| Big step evaluation of a checkable term in a given environment
  partial
  evalCheck : Check -> Env -> Value

  evalInfer (Ann t _) env = evalCheck t env
  evalInfer (Bnd x) env = case inBounds x env of
    Yes prf => index x env
    No nprf => idris_crash "OOPS"
  evalInfer (Var x) env = vfree x
  evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

  evalCheck (Emb i) env = evalInfer i env
  evalCheck (Lam b) env = VLam (\ v => evalCheck b (v :: env))


  data Kind =
    ||| We have a unique kind star for known base types
    Star

  ||| Names in scope either have an associated
  ||| Kind (they're base types) or
  ||| Ty (they're term variables)
  data Info : Type where
    HasKind : Kind -> Info
    HasType : Ty -> Info

  ||| A context is a list of names and their associated info
  Context : Type
  Context = List (Name, Info)

  parameters {0 m : Type -> Type} {auto _ : MonadError String m}

    ||| Checking a type's kinding
    kind : Context -> Kind -> Ty -> m ()
    kind ctx Star (Base x) = do
      let Just (HasKind Star) = lookup x ctx
         | Just _ => throwError "invalid identifier"
         | _ => throwError "unknown identifier"
      pure ()
    kind ctx Star (i ~> o) = do
      kind ctx Star i
      kind ctx Star o

    ||| Inference
    inferI : Nat -> Context -> Infer -> m Ty
    ||| Checking
    checkI : Nat -> Context -> Ty -> Check -> m ()

    inferI lvl ctx (Ann t ty) = do
      kind ctx Star ty
      ty <$ checkI lvl ctx ty t
    inferI lvl ctx (Bnd x) =
      -- unhandled in the original Haskell
      throwError "Oops"
    inferI lvl ctx (Var v) = do
      let Just (HasType ty) = lookup v ctx
        | Just _ => throwError "invalid identifier"
        | _ => throwError "unknown identifier"
      pure ty
    inferI lvl ctx (App f t) = do
      (i ~> o) <- inferI lvl ctx f
        | _ => throwError "illegal application"
      o <$ checkI lvl ctx i t


    checkI lvl ctx ty (Emb t) = do
      ty' <- inferI lvl ctx t
      unless (ty == ty') $ throwError "type mismatch"

    checkI lvl ctx ty (Lam b) = do
      let (i ~> o) = ty
        | _ => throwError "expected a function type"
      let x = Local lvl
      let k = HasType i
      let b = substCheck 0 (Var x) b
      checkI (S lvl) ((x, k) :: ctx) o b

    infer : Context -> Infer -> m Ty
    infer = inferI 0

    check : Context -> Ty -> Check -> m ()
    check = checkI 0

  exampleC : check [(Global "o", HasKind Star)]
                   (let ty = Base (Global "o") in (ty ~> ty) ~> ty ~> ty)
                   (Lam (Lam (Emb (Bnd 0))))
           = Right {a = String} ()
  exampleC = Refl

  boundFree : Nat -> Name -> Infer
  boundFree lvl (Quote i) = Bnd (minus lvl (S i))
  boundFree lvl x = Var x

  quoteStuckI : Nat -> Stuck -> Infer
  quoteValueI : Nat -> Value -> Check

  quoteStuckI lvl (NVar nm) = boundFree lvl nm
  quoteStuckI lvl (NApp e t) = App (quoteStuckI lvl e) (quoteValueI lvl t)

  quoteValueI lvl (VLam f) = Lam (quoteValueI (S lvl) (f (vfree (Quote lvl))))
  quoteValueI lvl (VEmb e) = Emb (quoteStuckI lvl e)

  quoteValue : Value -> Check
  quoteValue = quoteValueI 0

  partial
  normCheck : Check -> Env -> Check
  normCheck t env = quoteValue (evalCheck t env)

  partial
  normInfer : Infer -> Env -> Check
  normInfer t env = quoteValue (evalInfer t env)

  exampleQ : quoteValue (VLam $ \x => VLam $ \y => x)
           = Lam (Lam (Emb (Bnd 1)))
  exampleQ = Refl


  namespace Infer
    public export
    fromInteger : Integer -> Infer
    fromInteger n = Bnd (cast n)

  namespace Check
    public export
    fromString : String -> Check
    fromString x = Emb (Var (Global x))

    public export
    fromInteger : Integer -> Check
    fromInteger n = Emb (Bnd (cast n))

  ID, CONST : Check
  ID = Lam 0
  CONST = Lam (Lam 1)

  namespace Ty
    public export
    fromString : String -> Ty
    fromString x = Base (Global x)

  Term1 : Infer
  Term1 = Ann ID ("a" ~> "a") `App` "y"

  Ctx1 : Context
  Ctx1 = [(Global "y", HasType "a"), (Global "a", HasKind Star)]

  Term2 : Infer
  Term2 = Ann CONST (("b" ~> "b") ~> "a" ~> "b" ~> "b")
          `App` ID `App` "y"

  Ctx2 : Context
  Ctx2 = (Global "b", HasKind Star) :: Ctx1

  test0 : normInfer Term1 [] === "y"
  test0 = Refl

  test1 : normInfer Term2 [] === ID
  test1 = Refl

  test2 : infer Ctx1 Term1 === Right {a = String} "a"
  test2 = Refl

  test3 : infer Ctx2 Term2 === Right {a = String} ("b" ~> "b")
  test3 = Refl

%hide Infer
%hide Check
%hide Value
%hide Stuck

namespace Section3

  -- 3.4: Implementation

  data Infer : Type
  data Check : Type

  total
  data Infer : Type where
    ||| A checkable term annotated with its expected type
    Ann : (t, ty : Check) -> Infer
    ||| The star kind is inferrable
    Star : Infer
    ||| Pi is inferrable
    Pi : (a, b : Check) -> Infer
    ||| A bound variable
    Bnd : (k : Nat) -> Infer
    ||| A free variable
    Var : (nm : Name) -> Infer
    ||| The application of a function to its argument
    App : Infer -> Check -> Infer

  infixl 3 `App`

  %name Infer e, f

  total
  data Check : Type where
    ||| Inferable terms are trivially checkable
    Emb : Infer -> Check
    ||| A function binding its argument
    Lam : Check -> Check

  Eq Infer
  Eq Check

  Eq Infer where
    Ann t ty == Ann t' ty' = t == t' && ty == ty'
    Star == Star = True
    Pi a b == Pi s t = a == s && b == t
    Bnd k == Bnd l = k == l
    Var m == Var n = m == n
    App e s == App f t = e == f && s == t
    _ == _ = False

  Eq Check where
    Emb e == Emb f = assert_total (e == f)
    Lam b == Lam t = b == t
    _ == _ = False

  substCheck : Nat -> Infer -> Check -> Check
  substInfer : Nat -> Infer -> Infer -> Infer

  substCheck lvl u (Emb t) = Emb (substInfer lvl u t)
  substCheck lvl u (Lam b) = Lam (substCheck (S lvl) u b)

  substInfer lvl u (Ann s a) = Ann (substCheck lvl u s) (substCheck lvl u a)
  substInfer lvl u Star = Star
  substInfer lvl u (Pi a b) = Pi (substCheck lvl u a) (substCheck lvl u b)
  substInfer lvl u (Bnd k) = ifThenElse (lvl == k) u (Bnd k)
  substInfer lvl u (Var nm) = Var nm
  substInfer lvl u (App e s) = App (substInfer lvl u e) (substCheck lvl u s)

  %name Check s, t

  data Value : Type
  data Stuck : Type

  data Value : Type where
    ||| Lambda abstractions become functions in the host language
    VLam  : (b : Value -> Value) -> Value
    ||| The Star kind is a value already
    VStar : Value
    ||| Pi constructors combine a value for their domain and
    ||| a function in the host language for their codomain
    VPi   : (a : Value) -> (b : Value -> Value) -> Value
    ||| Stuck computations qualify as values
    VEmb  : (e : Stuck) -> Value

  data Stuck : Type where
    ||| A variable is a stuck computation
    NVar : Name -> Stuck
    ||| An application whose function is stuck is also stuck
    NApp : Stuck -> Value -> Stuck

  ||| Types are just values in TT
  Ty : Type
  Ty = Value

  ||| A context maps names to types, that is to say values
  Context : Type
  Context = List (Name, Ty)

  ||| We can easily turn a name into a value
  ||| by building a stuck computation first
  vfree : Name -> Value
  vfree x = VEmb (NVar x)

  ||| We can easily apply a value standing for a function
  ||| to a value standing for its argument by either deploying
  ||| the function or growing the spine of the stuck computation.
  partial
  vapp : Value -> Value -> Value
  vapp (VLam f) t = f t
  vapp (VEmb n) t = VEmb (NApp n t)
  vapp _ _ = idris_crash "Oops"

  ||| An environment is a list of values for all the bound variables in scope
  Env : Type
  Env = List Value

  ||| Big step evaluation of an inferrable term in a given environment
  partial
  evalInfer : Infer -> Env -> Value

  ||| Big step evaluation of a checkable term in a given environment
  partial
  evalCheck : Check -> Env -> Value

  evalInfer (Ann t _) env = evalCheck t env
  evalInfer Star env = VStar
  evalInfer (Pi a b) env = VPi (evalCheck a env) (\ v => evalCheck b (v :: env))
  evalInfer (Bnd x) env = case inBounds x env of
    Yes prf => index x env
    No nprf => idris_crash "OOPS"
  evalInfer (Var x) env = vfree x
  evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

  evalCheck (Emb i) env = evalInfer i env
  evalCheck (Lam b) env = VLam (\ v => evalCheck b (v :: env))


  boundFree : Nat -> Name -> Infer
  boundFree lvl (Quote i) = Bnd (minus lvl (S i))
  boundFree lvl x = Var x

  quoteStuckI : Nat -> Stuck -> Infer
  quoteValueI : Nat -> Value -> Check

  quoteStuckI lvl (NVar nm) = boundFree lvl nm
  quoteStuckI lvl (NApp e t) = App (quoteStuckI lvl e) (quoteValueI lvl t)

  quoteValueI lvl VStar = Emb Star
  quoteValueI lvl (VPi a b)
    = let a = quoteValueI lvl a in
      let x = vfree (Quote lvl) in
      let b = quoteValueI (S lvl) (b x) in
      Emb (Pi a b)
  quoteValueI lvl (VLam f) = Lam (quoteValueI (S lvl) (f (vfree (Quote lvl))))
  quoteValueI lvl (VEmb e) = Emb (quoteStuckI lvl e)

  quoteValue : Value -> Check
  quoteValue = quoteValueI 0

  partial
  normCheck : Check -> Env -> Check
  normCheck t env = quoteValue (evalCheck t env)

  partial
  normInfer : Infer -> Env -> Check
  normInfer t env = quoteValue (evalInfer t env)

  parameters {0 m : Type -> Type} {auto _ : MonadError String m}

    inferI : Nat -> Context -> Infer -> m Ty
    checkI : Nat -> Context -> Ty -> Check -> m ()

    inferI lvl ctx (Ann t ty) = do
      checkI lvl ctx VStar ty
      let ty = assert_total (evalCheck ty [])
      ty <$ checkI lvl ctx ty t
    inferI lvl ctx Star = pure VStar
    inferI lvl ctx (Pi a b) = do
      checkI lvl ctx VStar a
      let a = assert_total (evalCheck a [])
      let x = Local lvl
      let b = substCheck 0 (Var x) b
      checkI (S lvl) ((x, a) :: ctx) VStar b
      pure VStar
    inferI lvl ctx (Bnd k) =
      -- unhandled in the original Haskell
      throwError "Oops"
    inferI lvl ctx (Var v) = do
      let Just ty = lookup v ctx
        | _ => throwError "unknown identifier"
      pure ty
    inferI lvl ctx (App f t) = do
      (VPi a b) <- inferI lvl ctx f
        | _ => throwError "illegal application"
      checkI lvl ctx a t
      let t = assert_total (evalCheck t [])
      pure (b t)


    checkI lvl ctx ty (Emb t) = do
      ty' <- inferI lvl ctx t
      unless (quoteValue ty == quoteValue ty') $ throwError "type mismatch"
    checkI lvl ctx ty (Lam t) = do
      let VPi a b = ty
        | _ => throwError "expected a function type"
      let x = Local lvl
      checkI (S lvl) ((x, a) :: ctx) (b (vfree x)) t

%hide Infer
%hide Check

||| Section 4: Beyond LambdaPi
namespace Section4

  -- Section 4.1 Implementing natural numbers

  data Infer : Type
  data Check : Type

  total
  data Infer : Type where
    ||| A checkable term annotated with its expected type
    Ann : (t, ty : Check) -> Infer
    ||| The star kind is inferrable
    Star : Infer
    ||| The nat type is inferrable
    Nat : Infer
    ||| The nat induction principle is inferrable
    Rec : (pred, pz, ps : Check) -> (n : Check) -> Infer
    ||| The zero constructor is inferable
    Zro : Infer
    ||| The successor constructor is inferable
    Suc : Check -> Infer
    ||| Pi is inferrable
    Pi : (a, b : Check) -> Infer
    ||| A bound variable
    Bnd : (k : Nat) -> Infer
    ||| A free variable
    Var : (nm : Name) -> Infer
    ||| The application of a function to its argument
    App : Infer -> Check -> Infer

  infixl 3 `App`

  %name Infer e, f

  total
  data Check : Type where
    ||| Inferable terms are trivially checkable
    Emb : Infer -> Check
    ||| A function binding its argument
    Lam : Check -> Check

  Eq Infer
  Eq Check

  Eq Infer where
    Ann t ty == Ann t' ty' = t == t' && ty == ty'
    Star == Star = True
    Pi a b == Pi s t = a == s && b == t
    Bnd k == Bnd l = k == l
    Var m == Var n = m == n
    App e s == App f t = e == f && s == t
    _ == _ = False

  Eq Check where
    Emb e == Emb f = assert_total (e == f)
    Lam b == Lam t = b == t
    _ == _ = False

  substCheck : Nat -> Infer -> Check -> Check
  substInfer : Nat -> Infer -> Infer -> Infer

  substCheck lvl u (Emb t) = Emb (substInfer lvl u t)
  substCheck lvl u (Lam b) = Lam (substCheck (S lvl) u b)

  substInfer lvl u (Ann s a) = Ann (substCheck lvl u s) (substCheck lvl u a)
  substInfer lvl u Star = Star
  substInfer lvl u Nat = Nat
  substInfer lvl u Zro = Zro
  substInfer lvl u (Suc n) = Suc (substCheck lvl u n)
  substInfer lvl u (Rec p pz ps n)
    = Rec (substCheck lvl u p) (substCheck lvl u pz) (substCheck lvl u ps) (substCheck lvl u n)
  substInfer lvl u (Pi a b) = Pi (substCheck lvl u a) (substCheck lvl u b)
  substInfer lvl u (Bnd k) = ifThenElse (lvl == k) u (Bnd k)
  substInfer lvl u (Var nm) = Var nm
  substInfer lvl u (App e s) = App (substInfer lvl u e) (substCheck lvl u s)

  %name Check s, t

  data Value : Type
  data Stuck : Type

  data Value : Type where
    ||| Lambda abstractions become functions in the host language
    VLam  : (b : Value -> Value) -> Value
    ||| The Star kind is a value already
    VStar : Value
    ||| The nat type is a value already
    VNat : Value
    ||| The zero constructor is avalue
    VZro : Value
    ||| The successor constructor is a value constructor
    VSuc : Value -> Value
    ||| Pi constructors combine a value for their domain and
    ||| a function in the host language for their codomain
    VPi   : (a : Value) -> (b : Value -> Value) -> Value
    ||| Stuck computations qualify as values
    VEmb  : (e : Stuck) -> Value

  data Stuck : Type where
    ||| A variable is a stuck computation
    NVar : Name -> Stuck
    ||| An application whose function is stuck is also stuck
    NApp : Stuck -> Value -> Stuck
    ||| An induction principle applied to a stuck natural numnber is stuck
    NRec : (pred, pz, ps : Value) -> Stuck -> Stuck

  ||| Types are just values in TT
  Ty : Type
  Ty = Value

  ||| A context maps names to types, that is to say values
  Context : Type
  Context = List (Name, Ty)

  ||| We can easily turn a name into a value
  ||| by building a stuck computation first
  vfree : Name -> Value
  vfree x = VEmb (NVar x)

  infixl 5 `vapp`

  ||| We can easily apply a value standing for a function
  ||| to a value standing for its argument by either deploying
  ||| the function or growing the spine of the stuck computation.
  partial
  vapp : Value -> Value -> Value
  vapp (VLam f) t = f t
  vapp (VEmb n) t = VEmb (NApp n t)
  vapp _ _ = idris_crash "Oops"

  ||| An environment is a list of values for all the bound variables in scope
  Env : Type
  Env = List Value

  ||| Big step evaluation of an inferrable term in a given environment
  partial
  evalInfer : Infer -> Env -> Value

  ||| Big step evaluation of a checkable term in a given environment
  partial
  evalCheck : Check -> Env -> Value

  evalInfer (Ann t _) env = evalCheck t env
  evalInfer Star env = VStar
  evalInfer Nat env = VNat
  evalInfer Zro env = VZro
  evalInfer (Suc n) env = VSuc (evalCheck n env)
  evalInfer (Rec p pz ps n) env = go (evalCheck pz env) (evalCheck ps env) (evalCheck n env) where

    go : (pz, ps, n : Value) -> Value
    go pz ps VZro = pz
    go pz ps (VSuc n) = ps `vapp` n `vapp` (go pz ps n)
    go pz ps (VEmb n) = VEmb (NRec (evalCheck p env) pz ps n)
    go _ _ _ = idris_crash "Oops"

  evalInfer (Pi a b) env = VPi (evalCheck a env) (\ v => evalCheck b (v :: env))
  evalInfer (Bnd x) env = case inBounds x env of
    Yes prf => index x env
    No nprf => idris_crash "OOPS"
  evalInfer (Var x) env = vfree x
  evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

  evalCheck (Emb i) env = evalInfer i env
  evalCheck (Lam b) env = VLam (\ v => evalCheck b (v :: env))


  boundFree : Nat -> Name -> Infer
  boundFree lvl (Quote i) = Bnd (minus lvl (S i))
  boundFree lvl x = Var x

  quoteStuckI : Nat -> Stuck -> Infer
  quoteValueI : Nat -> Value -> Check

  quoteStuckI lvl (NVar nm) = boundFree lvl nm
  quoteStuckI lvl (NApp e t) = App (quoteStuckI lvl e) (quoteValueI lvl t)
  quoteStuckI lvl (NRec p pz ps n)
    = Rec (quoteValueI lvl p) (quoteValueI lvl pz) (quoteValueI lvl ps) (Emb (quoteStuckI lvl n))

  quoteValueI lvl VStar = Emb Star
  quoteValueI lvl VNat = Emb Nat
  quoteValueI lvl VZro = Emb Zro
  quoteValueI lvl (VSuc n) = Emb (Suc (quoteValueI lvl n))
  quoteValueI lvl (VPi a b)
    = let a = quoteValueI lvl a in
      let x = vfree (Quote lvl) in
      let b = quoteValueI (S lvl) (b x) in
      Emb (Pi a b)
  quoteValueI lvl (VLam f) = Lam (quoteValueI (S lvl) (f (vfree (Quote lvl))))
  quoteValueI lvl (VEmb e) = Emb (quoteStuckI lvl e)

  quoteValue : Value -> Check
  quoteValue = quoteValueI 0

  partial
  normCheck : Check -> Env -> Check
  normCheck t env = quoteValue (evalCheck t env)

  partial
  normInfer : Infer -> Env -> Check
  normInfer t env = quoteValue (evalInfer t env)

  parameters {0 m : Type -> Type} {auto _ : MonadError String m}

    inferI : Nat -> Context -> Infer -> m Ty
    checkI : Nat -> Context -> Ty -> Check -> m ()

    inferI lvl ctx (Ann t ty) = do
      checkI lvl ctx VStar ty
      let ty = assert_total (evalCheck ty [])
      ty <$ checkI lvl ctx ty t
    inferI lvl ctx Star = pure VStar
    inferI lvl ctx Nat = pure VStar
    inferI lvl ctx Zro = pure VNat
    inferI lvl ctx (Suc n) = VNat <$ checkI lvl ctx VNat n
    inferI lvl ctx (Rec p pz ps n) = do
      -- check & evaluate the predicate
      checkI lvl ctx (VPi VNat (\ _ => VStar)) p
      let p = assert_total (evalCheck p [])
      -- check pz has type (p 0)
      checkI lvl ctx (assert_total (p `vapp` VZro)) pz
      -- check ps has type (forall n. p n -> p (1+ n))
      let psTy = VPi VNat (\ n => VPi (p `vapp` n) (\ _ => p `vapp` VSuc n))
      checkI lvl ctx psTy ps
      -- check & evaluate the nat
      checkI lvl ctx VNat n
      let n = assert_total (evalCheck n [])
      -- return (p n)
      pure (assert_total (p `vapp` n))
    inferI lvl ctx (Pi a b) = do
      checkI lvl ctx VStar a
      let a = assert_total (evalCheck a [])
      let x = Local lvl
      let b = substCheck 0 (Var x) b
      checkI (S lvl) ((x, a) :: ctx) VStar b
      pure VStar
    inferI lvl ctx (Bnd k) =
      -- unhandled in the original Haskell
      throwError "Oops"
    inferI lvl ctx (Var v) = do
      let Just ty = lookup v ctx
        | _ => throwError "unknown identifier"
      pure ty
    inferI lvl ctx (App f t) = do
      (VPi a b) <- inferI lvl ctx f
        | _ => throwError "illegal application"
      checkI lvl ctx a t
      let t = assert_total (evalCheck t [])
      pure (b t)


    checkI lvl ctx ty (Emb t) = do
      ty' <- inferI lvl ctx t
      unless (quoteValue ty == quoteValue ty') $ throwError "type mismatch"
    checkI lvl ctx ty (Lam t) = do
      let VPi a b = ty
        | _ => throwError "expected a function type"
      let x = Local lvl
      checkI (S lvl) ((x, a) :: ctx) (b (vfree x)) t
