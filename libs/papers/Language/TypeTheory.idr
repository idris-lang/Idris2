||| The content of this module is based on the paper:
||| A tutorial implementation of a dependently typed lambda calculus
||| by Andres Löh, Conor McBride, and Wouter Swierstra
|||
||| NB: The work is originally written in Haskell and uses unsafe features
|||     This is not how we would write idiomatic Idris code.
|||     Cf. Language.IntrinsicScoping.TypeTheory for a more idiomatic representation.
module Language.TypeTheory

import Control.Monad.Error.Interface
import Data.List

%hide Prelude.Abs
%hide Prelude.MkAbs

%default covering

private infixl 3 `App`

||| We use this wrapper to mark places where binding occurs.
||| This is a major footgun and we hope the type constructor
||| forces users to think carefully about what they are doing
||| when they encounter Abs, thus potentially avoiding scoping bugs
||| given that scope is not an invariant here.
||| This is unfortunately not present in the original paper.
data Abs : Type -> Type where
   ||| The body of an abstraction lives in an extended context
   MkAbs : t -> Abs t

Eq t => Eq (Abs t) where
  MkAbs b == MkAbs b' = b == b'

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

  private infixr 0 ~>
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

  ||| Inferrable terms know what their type is
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

  %name Infer e, f

  total
  data Check : Type where
    ||| Inferrable terms are trivially checkable
    Emb : Infer -> Check
    ||| A function binding its argument
    Lam : Abs Check -> Check

  substCheck : Nat -> Infer -> Check -> Check
  substAbs   : Nat -> Infer -> Abs Check -> Abs Check
  substInfer : Nat -> Infer -> Infer -> Infer

  substCheck lvl u (Emb t) = Emb (substInfer lvl u t)
  substCheck lvl u (Lam b) = Lam (substAbs lvl u b)

  substAbs lvl u (MkAbs t) = MkAbs (substCheck (S lvl) u t)

  substInfer lvl u (Ann s a) = Ann (substCheck lvl u s) a
  substInfer lvl u (Bnd k) = ifThenElse (lvl == k) u (Bnd k)
  substInfer lvl u (Var nm) = Var nm
  substInfer lvl u (App e s) = App (substInfer lvl u e) (substCheck lvl u s)

  applyAbs : Abs Check -> Infer -> Check
  applyAbs (MkAbs t) u = substCheck 0 u t

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

  ||| Big step evaluation of an abstraction's body
  partial
  evalAbs : Abs Check -> Env -> Value -> Value
  evalAbs (MkAbs t) env v = evalCheck t (v :: env)

  evalInfer (Ann t _) env = evalCheck t env
  evalInfer (Bnd x) env = case inBounds x env of
    Yes prf => index x env
    No nprf => idris_crash "INTERNAL ERROR: evalInfer -> impossible case"
  evalInfer (Var x) env = vfree x
  evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

  evalCheck (Emb i) env = evalInfer i env
  evalCheck (Lam b) env = VLam (evalAbs b env)


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
      let b = applyAbs b (Var x)
      checkI (S lvl) ((x, k) :: ctx) o b

    infer : Context -> Infer -> m Ty
    infer = inferI 0

    check : Context -> Ty -> Check -> m ()
    check = checkI 0

  exampleC : check [(Global "o", HasKind Star)]
                   (let ty = Base (Global "o") in (ty ~> ty) ~> ty ~> ty)
                   (Lam (MkAbs (Lam (MkAbs (Emb (Bnd 0))))))
           = Right {a = String} ()
  exampleC = Refl

  boundFree : Nat -> Name -> Infer
  boundFree lvl (Quote i) = Bnd (minus lvl (S i))
  boundFree lvl x = Var x

  quoteStuckI : Nat -> Stuck -> Infer
  quoteValueI : Nat -> Value -> Check
  quoteAbsI   : Nat -> (Value -> Value) -> Abs Check

  quoteStuckI lvl (NVar nm) = boundFree lvl nm
  quoteStuckI lvl (NApp e t) = App (quoteStuckI lvl e) (quoteValueI lvl t)

  quoteValueI lvl (VLam f) = Lam (quoteAbsI lvl f)
  quoteValueI lvl (VEmb e) = Emb (quoteStuckI lvl e)

  quoteAbsI lvl f = MkAbs (quoteValueI (S lvl) (f (vfree (Quote lvl))))

  quoteValue : Value -> Check
  quoteValue = quoteValueI 0

  partial
  normCheck : Check -> Env -> Check
  normCheck t env = quoteValue (evalCheck t env)

  partial
  normInfer : Infer -> Env -> Check
  normInfer t env = quoteValue (evalInfer t env)

  exampleQ : quoteValue (VLam $ \x => VLam $ \y => x)
           = Lam (MkAbs (Lam (MkAbs (Emb (Bnd 1)))))
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
  ID = Lam (MkAbs 0)
  CONST = Lam (MkAbs (Lam (MkAbs 1)))

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
    Pi : (a : Check) -> (b : Abs Check) -> Infer
    ||| A bound variable
    Bnd : (k : Nat) -> Infer
    ||| A free variable
    Var : (nm : Name) -> Infer
    ||| The application of a function to its argument
    App : Infer -> Check -> Infer


  %name Infer e, f

  total
  data Check : Type where
    ||| Inferrable terms are trivially checkable
    Emb : Infer -> Check
    ||| A function binding its argument
    Lam : Abs Check -> Check

  Eq Infer
  Eq Check

  Eq Infer where
    Ann t ty == Ann t' ty' = t == t' && ty == ty'
    Star == Star = True
    Pi a b == Pi s t = a == s && assert_total (b == t)
    Bnd k == Bnd l = k == l
    Var m == Var n = m == n
    App e s == App f t = e == f && s == t
    _ == _ = False

  Eq Check where
    Emb e == Emb f = assert_total (e == f)
    Lam b == Lam t = assert_total (b == t)
    _ == _ = False

  substCheck : Nat -> Infer -> Check -> Check
  substAbs   : Nat -> Infer -> Abs Check -> Abs Check
  substInfer : Nat -> Infer -> Infer -> Infer

  substAbs lvl u (MkAbs b) = MkAbs (substCheck (S lvl) u b)


  substCheck lvl u (Emb t) = Emb (substInfer lvl u t)
  substCheck lvl u (Lam b) = Lam (substAbs lvl u b)

  substInfer lvl u (Ann s a) = Ann (substCheck lvl u s) (substCheck lvl u a)
  substInfer lvl u Star = Star
  substInfer lvl u (Pi a b) = Pi (substCheck lvl u a) (substAbs lvl u b)
  substInfer lvl u (Bnd k) = ifThenElse (lvl == k) u (Bnd k)
  substInfer lvl u (Var nm) = Var nm
  substInfer lvl u (App e s) = App (substInfer lvl u e) (substCheck lvl u s)

  applyAbs : Abs Check -> Infer -> Check
  applyAbs (MkAbs t) u = substCheck 0 u t

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
  vapp _ _ = idris_crash "INTERNAL ERROR: vapp -> impossible case"

  ||| An environment is a list of values for all the bound variables in scope
  Env : Type
  Env = List Value

  ||| Big step evaluation of an inferrable term in a given environment
  partial
  evalInfer : Infer -> Env -> Value

  ||| Big step evaluation of a checkable term in a given environment
  partial
  evalCheck : Check -> Env -> Value

  partial
  evalAbs : Abs Check -> Env -> Value -> Value
  evalAbs (MkAbs t) env v = evalCheck t (v :: env)


  evalInfer (Ann t _) env = evalCheck t env
  evalInfer Star env = VStar
  evalInfer (Pi a b) env = VPi (evalCheck a env) (evalAbs b env)
  evalInfer (Bnd x) env = case inBounds x env of
    Yes prf => index x env
    No nprf => idris_crash "INTERNAL ERROR: evalInfer -> impossible case"
  evalInfer (Var x) env = vfree x
  evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

  evalCheck (Emb i) env = evalInfer i env
  evalCheck (Lam b) env = VLam (evalAbs b env)


  boundFree : Nat -> Name -> Infer
  boundFree lvl (Quote i) = Bnd (minus lvl (S i))
  boundFree lvl x = Var x

  quoteStuckI : Nat -> Stuck -> Infer
  quoteValueI : Nat -> Value -> Check
  quoteAbsI   : Nat -> (Value -> Value) -> Abs Check

  quoteStuckI lvl (NVar nm) = boundFree lvl nm
  quoteStuckI lvl (NApp e t) = App (quoteStuckI lvl e) (quoteValueI lvl t)

  quoteValueI lvl VStar = Emb Star
  quoteValueI lvl (VPi a b)
    = let a = quoteValueI lvl a in
      let b = quoteAbsI lvl b in
      Emb (Pi a b)
  quoteValueI lvl (VLam f) = Lam (quoteAbsI lvl f)
  quoteValueI lvl (VEmb e) = Emb (quoteStuckI lvl e)

  quoteAbsI lvl f =
    let x = vfree (Quote lvl) in
    MkAbs (quoteValueI (S lvl) (f x))


  quoteValue : Value -> Check
  quoteValue = quoteValueI 0

  partial
  normCheck : Check -> Env -> Check
  normCheck t env = quoteValue (evalCheck t env)

  partial
  normInfer : Infer -> Env -> Check
  normInfer t env = quoteValue (evalInfer t env)

  parameters {0 m : Type -> Type} {auto _ : MonadError String m}

    inferI    : Nat -> Context -> Infer -> m Ty
    checkI    : Nat -> Context -> Ty -> Check -> m ()
    checkAbsI : Nat -> Context -> Ty -> (Ty -> Ty) -> Abs Check -> m ()

    inferI lvl ctx (Ann t ty) = do
      checkI lvl ctx VStar ty
      let ty = assert_total (evalCheck ty [])
      ty <$ checkI lvl ctx ty t
    inferI lvl ctx Star = pure VStar
    inferI lvl ctx (Pi a b) = do
      checkI lvl ctx VStar a
      let a = assert_total (evalCheck a [])
      let x = Local lvl
      VStar <$ checkAbsI lvl ctx a (\ _ => VStar) b
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
      checkAbsI lvl ctx a b t

  checkAbsI lvl ctx a b t = do
      let x = Local lvl
      let b = b (vfree x)
      let t = applyAbs t (Var x)
      checkI (S lvl) ((x, a) :: ctx) b t

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
    -- Here there's a bit of leeway in the design: we could just as well demand:
    --   pred : Abs Check
    --   pz : Check
    --   ps : Abs (Abs Check)
    --   n : Check
    Rec : (pred, pz, ps : Check) -> (n : Check) -> Infer
    ||| The zero constructor is inferrable
    Zro : Infer
    ||| The successor constructor is inferrable
    Suc : Check -> Infer
    ||| Pi is inferrable
    Pi : (a : Check) -> (b : Abs Check) -> Infer
    ||| A bound variable
    Bnd : (k : Nat) -> Infer
    ||| A free variable
    Var : (nm : Name) -> Infer
    ||| The application of a function to its argument
    App : Infer -> Check -> Infer

  %name Infer e, f

  total
  data Check : Type where
    ||| Inferrable terms are trivially checkable
    Emb : Infer -> Check
    ||| A function binding its argument
    Lam : Abs Check -> Check

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
    Lam b == Lam t = assert_total (b == t)
    _ == _ = False

  substCheck : Nat -> Infer -> Check -> Check
  substAbs   : Nat -> Infer -> Abs Check -> Abs Check
  substInfer : Nat -> Infer -> Infer -> Infer

  substCheck lvl u (Emb t) = Emb (substInfer lvl u t)
  substCheck lvl u (Lam b) = Lam (substAbs lvl u b)

  substInfer lvl u (Ann s a) = Ann (substCheck lvl u s) (substCheck lvl u a)
  substInfer lvl u Star = Star
  substInfer lvl u Nat = Nat
  substInfer lvl u Zro = Zro
  substInfer lvl u (Suc n) = Suc (substCheck lvl u n)
  substInfer lvl u (Rec p pz ps n)
    = Rec (substCheck lvl u p) (substCheck lvl u pz) (substCheck lvl u ps) (substCheck lvl u n)
  substInfer lvl u (Pi a b) = Pi (substCheck lvl u a) (substAbs lvl u b)
  substInfer lvl u (Bnd k) = ifThenElse (lvl == k) u (Bnd k)
  substInfer lvl u (Var nm) = Var nm
  substInfer lvl u (App e s) = App (substInfer lvl u e) (substCheck lvl u s)

  substAbs lvl u (MkAbs t) = MkAbs (substCheck (S lvl) u t)

  applyAbs : Abs Check -> Infer -> Check
  applyAbs (MkAbs t) u = substCheck 0 u t

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

  private infixl 5 `vapp`

  ||| We can easily apply a value standing for a function
  ||| to a value standing for its argument by either deploying
  ||| the function or growing the spine of the stuck computation.
  partial
  vapp : Value -> Value -> Value
  vapp (VLam f) t = f t
  vapp (VEmb n) t = VEmb (NApp n t)
  vapp _ _ = idris_crash "INTERNAL ERROR: vapp -> impossible case"

  ||| An environment is a list of values for all the bound variables in scope
  Env : Type
  Env = List Value

  ||| Big step evaluation of an inferrable term in a given environment
  partial
  evalInfer : Infer -> Env -> Value

  ||| Big step evaluation of a checkable term in a given environment
  partial
  evalCheck : Check -> Env -> Value

  ||| Big step evaluation of an abstraction in a given environment
  partial
  evalAbs : Abs Check -> Env -> Value -> Value
  evalAbs (MkAbs t) env v = evalCheck t (v :: env)

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
    go _ _ _ = idris_crash "INTERNAL ERROR: evalInfer -> impossible case"

  evalInfer (Pi a b) env = VPi (evalCheck a env) (evalAbs b env)
  evalInfer (Bnd x) env = case inBounds x env of
    Yes prf => index x env
    No nprf => idris_crash "INTERNAL ERROR: evalInfer -> impossible case"
  evalInfer (Var x) env = vfree x
  evalInfer (App f t) env = vapp (evalInfer f env) (evalCheck t env)

  evalCheck (Emb i) env = evalInfer i env
  evalCheck (Lam b) env = VLam (evalAbs b env)


  boundFree : Nat -> Name -> Infer
  boundFree lvl (Quote i) = Bnd (minus lvl (S i))
  boundFree lvl x = Var x

  quoteStuckI : Nat -> Stuck -> Infer
  quoteAbsI   : Nat -> (Value -> Value) -> Abs Check
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
      let b = quoteAbsI lvl b in
      Emb (Pi a b)
  quoteValueI lvl (VLam f) = Lam (quoteAbsI lvl f)
  quoteValueI lvl (VEmb e) = Emb (quoteStuckI lvl e)

  quoteAbsI lvl f = let x = vfree (Quote lvl) in MkAbs (quoteValueI (S lvl) (f x))

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
    checkAbsI : Nat -> Context -> Ty -> (Ty -> Ty) -> Abs Check -> m ()
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
      VStar <$ checkAbsI lvl ctx a (\ _ => VStar) b
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
      checkAbsI lvl ctx a b t


  checkAbsI lvl ctx a b t = do
      let x = Local lvl
      let b = b (vfree x)
      let t = applyAbs t (Var x)
      checkI (S lvl) ((x, a) :: ctx) b t
