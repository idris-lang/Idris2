module Core.TT

import public Core.FC
import public Core.Name
import public Core.Name.Scoped


import Idris.Pretty.Annotations

import Data.List
import Data.Nat
import Data.String
import Data.Vect
import Decidable.Equality

import Libraries.Data.NameMap
import Libraries.Data.Primitives
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Data.String.Extra

import Libraries.Data.List.HasLength
import Libraries.Data.List.SizeOf

import public Algebra

import public Core.TT.Primitive
import public Core.TT.Binder

%default covering

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

%name NameType nt

export
covering
Show NameType where
  showPrec d Bound = "Bound"
  showPrec d Func = "Func"
  showPrec d (DataCon tag ar) = showCon d "DataCon" $ showArg tag ++ showArg ar
  showPrec d (TyCon tag ar) = showCon d "TyCon" $ showArg tag ++ showArg ar

export
isCon : NameType -> Maybe (Int, Nat)
isCon (DataCon t a) = Just (t, a)
isCon (TyCon t a) = Just (t, a)
isCon _ = Nothing

public export
record KindedName where
  constructor MkKindedName
  nameKind : Maybe NameType
  fullName : Name -- fully qualified name
  rawName  : Name

%name KindedName kn

export
defaultKindedName : Name -> KindedName
defaultKindedName nm = MkKindedName Nothing nm nm

export
funKindedName : Name -> KindedName
funKindedName nm = MkKindedName (Just Func) nm nm

export
Show KindedName where show = show . rawName

export
covering
[Raw] Show KindedName where
  showPrec d (MkKindedName nm fn rn) =
    showCon d "MkKindedName" $ showArg nm ++ showArg @{Raw} fn ++ showArg @{Raw} rn


public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

%name IsVar idx

export
dropLater : IsVar nm (S idx) (v :: vs) -> IsVar nm idx vs
dropLater (Later p) = p

export
mkVar : (wkns : List Name) -> IsVar nm (length wkns) (wkns ++ nm :: vars)
mkVar [] = First
mkVar (w :: ws) = Later (mkVar ws)

public export
dropVar : (ns : List Name) -> {idx : Nat} -> (0 p : IsVar name idx ns) -> List Name
dropVar (n :: xs) First = xs
dropVar (n :: xs) (Later p) = n :: dropVar xs p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

namespace Var

  export
  later : Var ns -> Var (n :: ns)
  later (MkVar p) = MkVar (Later p)

export
sameVar : Var xs -> Var xs -> Bool
sameVar (MkVar {i=x} _) (MkVar {i=y} _) = x == y

export
varIdx : Var xs -> Nat
varIdx (MkVar {i} _) = i

export
dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

export
Show (Var ns) where
  show (MkVar {i} _) = show i

namespace CList
  -- A list correspoding to another list
  public export
  data CList : List a -> Type -> Type where
       Nil : CList [] ty
       (::) : (x : ty) -> CList cs ty -> CList (c :: cs) ty

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data LazyReason = LInf | LLazy | LUnknown

%name LazyReason lz

-- For as patterns matching linear arguments, select which side is
-- consumed
public export
data UseSide = UseLeft | UseRight

%name UseSide side

public export
data WhyErased a
  = Placeholder
  | Impossible
  | Dotted a

export
Show a => Show (WhyErased a) where
  show Placeholder = "placeholder"
  show Impossible = "impossible"
  show (Dotted x) = "dotted \{show x}"

%name WhyErased why

export
Functor WhyErased where
  map f Placeholder = Placeholder
  map f Impossible = Impossible
  map f (Dotted x) = Dotted (f x)

export
Foldable WhyErased where
  foldr c n (Dotted x) = c x n
  foldr c n _ = n

export
Traversable WhyErased where
  traverse f Placeholder = pure Placeholder
  traverse f Impossible = pure Impossible
  traverse f (Dotted x) = Dotted <$> f x

public export
data Term : List Name -> Type where
     Local : FC -> (isLet : Maybe Bool) ->
             (idx : Nat) -> (0 p : IsVar name idx vars) -> Term vars
     Ref : FC -> NameType -> (name : Name) -> Term vars
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Int -> List (Term vars) -> Term vars
     Bind : FC -> (x : Name) ->
            (b : Binder (Term vars)) ->
            (scope : Term (x :: vars)) -> Term vars
     App : FC -> (fn : Term vars) -> (arg : Term vars) -> Term vars
     -- as patterns; since we check LHS patterns as terms before turning
     -- them into patterns, this helps us get it right. When normalising,
     -- we just reduce the inner term and ignore the 'as' part
     -- The 'as' part should really be a Name rather than a Term, but it's
     -- easier this way since it gives us the ability to work with unresolved
     -- names (Ref) and resolved names (Local) without having to define a
     -- special purpose thing. (But it'd be nice to tidy that up, nevertheless)
     As : FC -> UseSide -> (as : Term vars) -> (pat : Term vars) -> Term vars
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vars -> Term vars
     TDelay : FC -> LazyReason -> (ty : Term vars) -> (arg : Term vars) -> Term vars
     TForce : FC -> LazyReason -> Term vars -> Term vars
     PrimVal : FC -> (c : Constant) -> Term vars
     Erased : FC -> WhyErased (Term vars) -> -- True == impossible term, for coverage checker
              Term vars
     TType : FC -> Name -> -- universe variable
             Term vars

%name Term t, u

-- Remove/restore the given namespace from all Refs. This is to allow
-- writing terms and case trees to disk without repeating the same namespace
-- all over the place.
public export
interface StripNamespace a where
  trimNS : Namespace -> a -> a
  restoreNS : Namespace -> a -> a

export
StripNamespace (Term vars) where
  trimNS ns tm@(Ref fc x (NS tns n))
      = if ns == tns then Ref fc x (NS (unsafeFoldNamespace []) n) else tm
        -- ^ A blank namespace, rather than a UN, so we don't catch primitive
        -- names which are represented as UN.
  trimNS ns (Meta fc x y xs)
      = Meta fc x y (map (trimNS ns) xs)
  trimNS ns (Bind fc x b scope)
      = Bind fc x (map (trimNS ns) b) (trimNS ns scope)
  trimNS ns (App fc fn arg)
      = App fc (trimNS ns fn) (trimNS ns arg)
  trimNS ns (As fc s p tm)
      = As fc s (trimNS ns p) (trimNS ns tm)
  trimNS ns (TDelayed fc x y)
      = TDelayed fc x (trimNS ns y)
  trimNS ns (TDelay fc x t y)
      = TDelay fc x (trimNS ns t) (trimNS ns y)
  trimNS ns (TForce fc r y)
      = TForce fc r (trimNS ns y)
  trimNS ns tm = tm

  restoreNS ns tm@(Ref fc x (NS tmns n))
      = if isNil (unsafeUnfoldNamespace tmns)
            then Ref fc x (NS ns n)
            else tm
  restoreNS ns (Meta fc x y xs)
      = Meta fc x y (map (restoreNS ns) xs)
  restoreNS ns (Bind fc x b scope)
      = Bind fc x (map (restoreNS ns) b) (restoreNS ns scope)
  restoreNS ns (App fc fn arg)
      = App fc (restoreNS ns fn) (restoreNS ns arg)
  restoreNS ns (As fc s p tm)
      = As fc s (restoreNS ns p) (restoreNS ns tm)
  restoreNS ns (TDelayed fc x y)
      = TDelayed fc x (restoreNS ns y)
  restoreNS ns (TDelay fc x t y)
      = TDelay fc x (restoreNS ns t) (restoreNS ns y)
  restoreNS ns (TForce fc r y)
      = TForce fc r (restoreNS ns y)
  restoreNS ns tm = tm

export
isErased : Term vars -> Bool
isErased (Erased _ _) = True
isErased _ = False

export
getLoc : Term vars -> FC
getLoc (Local fc _ _ _) = fc
getLoc (Ref fc _ _) = fc
getLoc (Meta fc _ _ _) = fc
getLoc (Bind fc _ _ _) = fc
getLoc (App fc _ _) = fc
getLoc (As fc _ _ _) = fc
getLoc (TDelayed fc _ _) = fc
getLoc (TDelay fc _ _ _) = fc
getLoc (TForce fc _ _) = fc
getLoc (PrimVal fc _) = fc
getLoc (Erased fc i) = fc
getLoc (TType fc _) = fc

export
Eq LazyReason where
  (==) LInf LInf = True
  (==) LLazy LLazy = True
  (==) LUnknown LUnknown = True
  (==) _ _ = False

export
Show LazyReason where
    show LInf = "Inf"
    show LLazy = "Lazy"
    show LUnknown = "Unkown"

export
compatible : LazyReason -> LazyReason -> Bool
compatible LUnknown _ = True
compatible _ LUnknown = True
compatible x y = x == y

export
eqBinderBy : (t -> u -> Bool) -> (Binder t -> Binder u -> Bool)
eqBinderBy eqTU = go where

  go : Binder t -> Binder u -> Bool
  go (Lam _ c p ty) (Lam _ c' p' ty') = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (Let _ c v ty) (Let _ c' v' ty') = c == c' && eqTU v v' && eqTU ty ty'
  go (Pi _ c p ty) (Pi _ c' p' ty')   = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (PVar _ c p ty) (PVar _ c' p' ty') = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (PLet _ c v ty) (PLet _ c' v' ty') = c == c' && eqTU v v' && eqTU ty ty'
  go (PVTy _ c ty) (PVTy _ c' ty') = c == c' && eqTU ty ty'
  go _ _ = False

export
Eq a => Eq (Binder a) where
  (==) = eqBinderBy (==)

export
total
Eq a => Eq (WhyErased a) where
  Placeholder == Placeholder = True
  Impossible == Impossible = True
  Dotted t == Dotted u = t == u
  _ == _ = False


export
total
Eq (Term vars) where
  (==) (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
  (==) (Ref _ _ n) (Ref _ _ n') = n == n'
  (==) (Meta _ _ i args) (Meta _ _ i' args')
      = i == i' && assert_total (args == args')
  (==) (Bind _ _ b sc) (Bind _ _ b' sc')
      = assert_total (b == b' && sc == believe_me sc')
  (==) (App _ f a) (App _ f' a') = f == f' && a == a'
  (==) (As _ _ a p) (As _ _ a' p') = a == a' && p == p'
  (==) (TDelayed _ _ t) (TDelayed _ _ t') = t == t'
  (==) (TDelay _ _ t x) (TDelay _ _ t' x') = t == t' && x == x'
  (==) (TForce _ _ t) (TForce _ _ t') = t == t'
  (==) (PrimVal _ c) (PrimVal _ c') = c == c'
  (==) (Erased _ i) (Erased _ i') = assert_total (i == i')
  (==) (TType _ _) (TType _ _) = True
  (==) _ _ = False

-- Check equality, ignoring variable naming and universes
eqWhyErased : WhyErased (Term vs) -> WhyErased (Term vs') -> Bool

export
total
eqTerm : Term vs -> Term vs' -> Bool
eqTerm (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
eqTerm (Ref _ _ n) (Ref _ _ n') = n == n'
eqTerm (Meta _ _ i args) (Meta _ _ i' args')
    = i == i' && assert_total (all (uncurry eqTerm) (zip args args'))
eqTerm (Bind _ _ b sc) (Bind _ _ b' sc')
    = assert_total (eqBinderBy eqTerm b b') && eqTerm sc sc'
eqTerm (App _ f a) (App _ f' a') = eqTerm f f' && eqTerm a a'
eqTerm (As _ _ a p) (As _ _ a' p') = eqTerm a a' && eqTerm p p'
eqTerm (TDelayed _ _ t) (TDelayed _ _ t') = eqTerm t t'
eqTerm (TDelay _ _ t x) (TDelay _ _ t' x') = eqTerm t t' && eqTerm x x'
eqTerm (TForce _ _ t) (TForce _ _ t') = eqTerm t t'
eqTerm (PrimVal _ c) (PrimVal _ c') = c == c'
eqTerm (Erased _ i) (Erased _ i') = eqWhyErased i i'
eqTerm (TType _ _) (TType _ _) = True
eqTerm _ _ = False

eqWhyErased Impossible Impossible = True
eqWhyErased Placeholder Placeholder = True
eqWhyErased (Dotted t) (Dotted u)  = eqTerm t u
eqWhyErased _ _ = False

public export
data Visibility = Private | Export | Public
%name Visibility vis

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Pretty Void Visibility where
  pretty Private = pretty "private"
  pretty Export = pretty "export"
  pretty Public = pretty "public" <++> pretty "export"

export
Eq Visibility where
  Private == Private = True
  Export == Export = True
  Public == Public = True
  _ == _ = False

export
Ord Visibility where
  compare Private Export = LT
  compare Private Public = LT
  compare Export Public = LT

  compare Private Private = EQ
  compare Export Export = EQ
  compare Public Public = EQ

  compare Export Private = GT
  compare Public Private = GT
  compare Public Export = GT

public export
data TotalReq = Total | CoveringOnly | PartialOK
%name TotalReq treq

export
Eq TotalReq where
    (==) Total Total = True
    (==) CoveringOnly CoveringOnly = True
    (==) PartialOK PartialOK = True
    (==) _ _ = False

||| Bigger means more requirements
||| So if a definition was checked at b, it can be accepted at a <= b.
export
Ord TotalReq where
  PartialOK <= _ = True
  _ <= Total = True
  a <= b = a == b

  a < b = a <= b && a /= b

export
Show TotalReq where
    show Total = "total"
    show CoveringOnly = "covering"
    show PartialOK = "partial"

public export
data PartialReason
       = NotStrictlyPositive
       | BadCall (List Name)
       -- sequence of mutually-recursive function calls leading to a non-terminating function
       | BadPath (List (FC, Name)) Name
       | RecPath (List (FC, Name))

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n])
      = "possibly not terminating due to call to " ++ show n
  show (BadCall ns)
      = "possibly not terminating due to calls to " ++ showSep ", " (map show ns)
  show (BadPath [_] n)
      = "possibly not terminating due to call  to " ++ show n
  show (BadPath init n)
      = "possibly not terminating due to function " ++ show n ++ " being reachable via " ++ showSep " -> " (map show init)
  show (RecPath loop)
      = "possibly not terminating due to recursive path " ++ showSep " -> " (map (show . snd) loop)

export
Pretty Void PartialReason where
  pretty NotStrictlyPositive = reflow "not strictly positive"
  pretty (BadCall [n])
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadCall ns)
    = reflow "possibly not terminating due to calls to" <++> concatWith (surround (comma <+> space)) (pretty <$> ns)
  pretty (BadPath [_] n)
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadPath init n)
    = reflow "possibly not terminating due to function" <++> pretty n
      <++> reflow "being reachable via"
      <++> concatWith (surround (pretty " -> ")) (pretty <$> map snd init)
  pretty (RecPath loop)
    = reflow "possibly not terminating due to recursive path" <++> concatWith (surround (pretty " -> ")) (pretty <$> map snd loop)

public export
data Terminating
       = Unchecked
       | IsTerminating
       | NotTerminating PartialReason

export
Show Terminating where
  show Unchecked = "not yet checked"
  show IsTerminating = "terminating"
  show (NotTerminating p) = show p

export
Pretty Void Terminating where
  pretty Unchecked = reflow "not yet checked"
  pretty IsTerminating = pretty "terminating"
  pretty (NotTerminating p) = pretty p

public export
data Covering
       = IsCovering
       | MissingCases (List (Term []))
       | NonCoveringCall (List Name)

export
Show Covering where
  show IsCovering = "covering"
  show (MissingCases c) = "not covering all cases"
  show (NonCoveringCall [f])
     = "not covering due to call to function " ++ show f
  show (NonCoveringCall cs)
     = "not covering due to calls to functions " ++ showSep ", " (map show cs)

export
Pretty Void Covering where
  pretty IsCovering = pretty "covering"
  pretty (MissingCases c) = reflow "not covering all cases"
  pretty (NonCoveringCall [f])
     = reflow "not covering due to call to function" <++> pretty f
  pretty (NonCoveringCall cs)
     = reflow "not covering due to calls to functions" <++> concatWith (surround (comma <+> space)) (pretty <$> cs)

-- Totality status of a definition. We separate termination checking from
-- coverage checking.
public export
record Totality where
     constructor MkTotality
     isTerminating : Terminating
     isCovering : Covering

export
Show Totality where
  show tot
    = let t = isTerminating tot
          c = isCovering tot in
        showTot t c
    where
      showTot : Terminating -> Covering -> String
      showTot IsTerminating IsCovering = "total"
      showTot IsTerminating c = show c
      showTot t IsCovering = show t
      showTot t c = show c ++ "; " ++ show t

export
Pretty Void Totality where
  pretty (MkTotality IsTerminating IsCovering) = pretty "total"
  pretty (MkTotality IsTerminating c) = pretty c
  pretty (MkTotality t IsCovering) = pretty t
  pretty (MkTotality t c) = pretty c <+> semi <++> pretty t

export
unchecked : Totality
unchecked = MkTotality Unchecked IsCovering

export
isTotal : Totality
isTotal = MkTotality Unchecked IsCovering

export
notCovering : Totality
notCovering = MkTotality Unchecked (MissingCases [])

public export
data NVar : Name -> List Name -> Type where
     MkNVar : {i : Nat} -> (0 p : IsVar n i vars) -> NVar n vars

namespace NVar
  export
  later : NVar nm ns -> NVar nm (n :: ns)
  later (MkNVar p) = MkNVar (Later p)

export
weakenNVar : SizeOf ns -> NVar name inner -> NVar name (ns ++ inner)
-- weakenNVar p x = case sizedView p of
--   Z     => x
--   (S p) => later (weakenNVar p x)
-- ^^^^ The above is the correct way, the below involves a proof which
-- is nonsense, but it's okay because it's deleted, and all we're doing is
-- adding a number so let's do it the quick way
weakenNVar (MkSizeOf s _)  (MkNVar {i} p)
    = (MkNVar {i = plus s i} (believe_me p))

export
insertNVar : SizeOf outer ->
             NVar nm (outer ++ inner) ->
             NVar nm (outer ++ n :: inner)
insertNVar p v = case sizedView p of
  Z     => later v
  (S p) => case v of
    MkNVar First     => MkNVar First
    MkNVar (Later v) => later (insertNVar p (MkNVar v))

export
insertVar : SizeOf outer ->
            Var (outer ++ inner) ->
            Var (outer ++ n :: inner)
insertVar p (MkVar v) = let MkNVar v' = insertNVar p (MkNVar v) in MkVar v'


||| The (partial) inverse to insertVar
export
removeVar : SizeOf outer ->
            Var        (outer ++ [x] ++ inner) ->
            Maybe (Var (outer        ++ inner))
removeVar out var = case sizedView out of
  Z => case var of
          MkVar First     => Nothing
          MkVar (Later p) => Just (MkVar p)
  S out' => case var of
              MkVar First     => Just (MkVar First)
              MkVar (Later p) => later <$> removeVar out' (MkVar p)

export
weakenVar : SizeOf ns -> Var inner -> Var (ns ++ inner)
weakenVar p (MkVar v) = let MkNVar v' = weakenNVar p (MkNVar v) in MkVar v'

export
insertNVarNames : SizeOf outer -> SizeOf ns ->
                  NVar name (outer ++ inner) ->
                  NVar name (outer ++ (ns ++ inner))
insertNVarNames p q v = case sizedView p of
  Z     => weakenNVar q v
  (S p) => case v of
    MkNVar First      => MkNVar First
    MkNVar (Later v') => later (insertNVarNames p q (MkNVar v'))

export
insertVarNames : SizeOf outer -> SizeOf ns ->
                 Var (outer ++ inner) ->
                 Var (outer ++ (ns ++ inner))
insertVarNames p q (MkVar v) = let MkNVar v' = insertNVarNames p q (MkNVar v) in MkVar v'

export
insertNames : SizeOf outer -> SizeOf ns ->
              Term (outer ++ inner) ->
              Term (outer ++ (ns ++ inner))
insertNames out ns (Local fc r idx prf)
   = let MkNVar prf' = insertNVarNames out ns (MkNVar prf) in
     Local fc r _ prf'
insertNames out ns (Ref fc nt name) = Ref fc nt name
insertNames out ns (Meta fc name idx args)
    = Meta fc name idx (map (insertNames out ns) args)
insertNames out ns (Bind fc x b scope)
    = Bind fc x (assert_total (map (insertNames out ns) b))
           (insertNames (suc out) ns scope)
insertNames out ns (App fc fn arg)
    = App fc (insertNames out ns fn) (insertNames out ns arg)
insertNames out ns (As fc s as tm)
    = As fc s (insertNames out ns as) (insertNames out ns tm)
insertNames out ns (TDelayed fc r ty) = TDelayed fc r (insertNames out ns ty)
insertNames out ns (TDelay fc r ty tm)
    = TDelay fc r (insertNames out ns ty) (insertNames out ns tm)
insertNames out ns (TForce fc r tm) = TForce fc r (insertNames out ns tm)
insertNames out ns (PrimVal fc c) = PrimVal fc c
insertNames out ns (Erased fc Impossible) = Erased fc Impossible
insertNames out ns (Erased fc Placeholder) = Erased fc Placeholder
insertNames out ns (Erased fc (Dotted t)) = Erased fc (Dotted (insertNames out ns t))
insertNames out ns (TType fc u) = TType fc u

export
Weaken Term where
  weakenNs p tm = insertNames zero p tm

export
Weaken Var where
  weaken = later
  -- TODO: replace with efficient version
  weakenNs s v = case sizedView s of
    Z => v
    S k => later (weakenNs k v)

export
varExtend : IsVar x idx xs -> IsVar x idx (xs ++ ys)
-- What Could Possibly Go Wrong?
-- This relies on the runtime representation of the term being the same
-- after embedding! It is just an identity function at run time, though, and
-- we don't need its definition at compile time, so let's do it...
varExtend p = believe_me p

export
FreelyEmbeddable Term where

public export
ClosedTerm : Type
ClosedTerm = Term []

export
apply : FC -> Term vars -> List (Term vars) -> Term vars
apply loc fn [] = fn
apply loc fn (a :: args) = apply loc (App loc fn a) args

-- Creates a chain of `App` nodes, each with its own file context
export
applyWithFC : Term vars -> List (FC, Term vars) -> Term vars
applyWithFC fn [] = fn
applyWithFC fn ((fc, arg) :: args) = applyWithFC (App fc fn arg) args

-- Build a simple function type
export
fnType : {vars : _} -> FC -> Term vars -> Term vars -> Term vars
fnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc top Explicit arg) (weaken scope)

export
linFnType : {vars : _} -> FC -> Term vars -> Term vars -> Term vars
linFnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc linear Explicit arg) (weaken scope)

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App _ f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFn : Term vars -> Term vars
getFn (App _ f a) = getFn f
getFn tm = tm

export
getArgs : Term vars -> (List (Term vars))
getArgs = snd . getFnArgs

renameLocalRef : CompatibleVars xs ys ->
                 {idx : Nat} ->
                 (0 p : IsVar name idx xs) ->
                 Var ys
renameLocalRef prf p = believe_me (MkVar p)
-- renameLocalRef Pre First = (MkVar First)
-- renameLocalRef (Ext x) First = (MkVar First)
-- renameLocalRef Pre (Later p) = (MkVar (Later p))
-- renameLocalRef (Ext y) (Later p)
--     = let (MkVar p') = renameLocalRef y p in MkVar (Later p')

renameVarList : CompatibleVars xs ys -> Var xs -> Var ys
renameVarList prf (MkVar p) = renameLocalRef prf p

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars compat tm = believe_me tm -- no names in term, so it's identity
-- This is how we would define it:
-- renameVars Pre tm = tm
-- renameVars prf (Local fc r idx vprf)
--     = let MkVar vprf' = renameLocalRef prf vprf in
--           Local fc r _ vprf'
-- renameVars prf (Ref fc x name) = Ref fc x name
-- renameVars prf (Meta fc n i args)
--     = Meta fc n i (map (renameVars prf) args)
-- renameVars prf (Bind fc x b scope)
--     = Bind fc x (map (renameVars prf) b) (renameVars (Ext prf) scope)
-- renameVars prf (App fc fn arg)
--     = App fc (renameVars prf fn) (renameVars prf arg)
-- renameVars prf (As fc s as tm)
--     = As fc s (renameVars prf as) (renameVars prf tm)
-- renameVars prf (TDelayed fc r ty) = TDelayed fc r (renameVars prf ty)
-- renameVars prf (TDelay fc r ty tm)
--     = TDelay fc r (renameVars prf ty) (renameVars prf tm)
-- renameVars prf (TForce fc r x) = TForce fc r (renameVars prf x)
-- renameVars prf (PrimVal fc c) = PrimVal fc c
-- renameVars prf (Erased fc i) = Erased fc i
-- renameVars prf (TType fc) = TType fc

export
renameTop : (m : Name) -> Term (n :: vars) -> Term (m :: vars)
renameTop m tm = renameVars (Ext Pre) tm

public export
data SubVars : List Name -> List Name -> Type where
     SubRefl  : SubVars xs xs
     DropCons : SubVars xs ys -> SubVars xs (y :: ys)
     KeepCons : SubVars xs ys -> SubVars (x :: xs) (x :: ys)

export
subElem : {idx : Nat} -> (0 p : IsVar name idx xs) ->
          SubVars ys xs -> Maybe (Var ys)
subElem prf SubRefl = Just (MkVar prf)
subElem First (DropCons p) = Nothing
subElem (Later x) (DropCons p)
    = do MkVar prf' <- subElem x p
         Just (MkVar prf')
subElem First (KeepCons p) = Just (MkVar First)
subElem (Later x) (KeepCons p)
    = do MkVar prf' <- subElem x p
         Just (MkVar (Later prf'))

export
subExtend : (ns : List Name) -> SubVars xs ys -> SubVars (ns ++ xs) (ns ++ ys)
subExtend [] sub = sub
subExtend (x :: xs) sub = KeepCons (subExtend xs sub)

export
subInclude : (ns : List Name) -> SubVars xs ys -> SubVars (xs ++ ns) (ys ++ ns)
subInclude ns SubRefl = SubRefl
subInclude ns (DropCons p) = DropCons (subInclude ns p)
subInclude ns (KeepCons p) = KeepCons (subInclude ns p)

mutual
  export
  shrinkPi : PiInfo (Term vars) -> SubVars newvars vars ->
             Maybe (PiInfo (Term newvars))
  shrinkPi Explicit prf = pure Explicit
  shrinkPi Implicit prf = pure Implicit
  shrinkPi AutoImplicit prf = pure AutoImplicit
  shrinkPi (DefImplicit t) prf = pure (DefImplicit !(shrinkTerm t prf))

  export
  shrinkBinder : Binder (Term vars) -> SubVars newvars vars ->
                 Maybe (Binder (Term newvars))
  shrinkBinder (Lam fc c p ty) prf
      = Just (Lam fc c !(shrinkPi p prf) !(shrinkTerm ty prf))
  shrinkBinder (Let fc c val ty) prf
      = Just (Let fc c !(shrinkTerm val prf) !(shrinkTerm ty prf))
  shrinkBinder (Pi fc c p ty) prf
      = Just (Pi fc c !(shrinkPi p prf) !(shrinkTerm ty prf))
  shrinkBinder (PVar fc c p ty) prf
      = Just (PVar fc c !(shrinkPi p prf) !(shrinkTerm ty prf))
  shrinkBinder (PLet fc c val ty) prf
      = Just (PLet fc c !(shrinkTerm val prf) !(shrinkTerm ty prf))
  shrinkBinder (PVTy fc c ty) prf
      = Just (PVTy fc c !(shrinkTerm ty prf))

  export
  shrinkVar : Var vars -> SubVars newvars vars -> Maybe (Var newvars)
  shrinkVar (MkVar x) prf = subElem x prf

  export
  shrinkTerm : Term vars -> SubVars newvars vars -> Maybe (Term newvars)
  shrinkTerm (Local fc r idx loc) prf = (\(MkVar loc') => Local fc r _ loc') <$> subElem loc prf
  shrinkTerm (Ref fc x name) prf = Just (Ref fc x name)
  shrinkTerm (Meta fc x y xs) prf
     = do xs' <- traverse (\x => shrinkTerm x prf) xs
          Just (Meta fc x y xs')
  shrinkTerm (Bind fc x b scope) prf
     = Just (Bind fc x !(shrinkBinder b prf) !(shrinkTerm scope (KeepCons prf)))
  shrinkTerm (App fc fn arg) prf
     = Just (App fc !(shrinkTerm fn prf) !(shrinkTerm arg prf))
  shrinkTerm (As fc s as tm) prf
     = Just (As fc s !(shrinkTerm as prf) !(shrinkTerm tm prf))
  shrinkTerm (TDelayed fc x y) prf
     = Just (TDelayed fc x !(shrinkTerm y prf))
  shrinkTerm (TDelay fc x t y) prf
     = Just (TDelay fc x !(shrinkTerm t prf) !(shrinkTerm y prf))
  shrinkTerm (TForce fc r x) prf
     = Just (TForce fc r !(shrinkTerm x prf))
  shrinkTerm (PrimVal fc c) prf = Just (PrimVal fc c)
  shrinkTerm (Erased fc Placeholder) prf = Just (Erased fc Placeholder)
  shrinkTerm (Erased fc Impossible) prf = Just (Erased fc Impossible)
  shrinkTerm (Erased fc (Dotted t)) prf = Erased fc . Dotted <$> shrinkTerm t prf
  shrinkTerm (TType fc u) prf = Just (TType fc u)

varEmbedSub : SubVars small vars ->
              {idx : Nat} -> (0 p : IsVar n idx small) ->
              Var vars
varEmbedSub SubRefl y = MkVar y
varEmbedSub (DropCons prf) y
    = let MkVar y' = varEmbedSub prf y in
          MkVar (Later y')
varEmbedSub (KeepCons prf) First = MkVar First
varEmbedSub (KeepCons prf) (Later p)
    = let MkVar p' = varEmbedSub prf p in
          MkVar (Later p')

export
embedSub : SubVars small vars -> Term small -> Term vars
embedSub sub (Local fc x idx y)
    = let MkVar y' = varEmbedSub sub y in Local fc x _ y'
embedSub sub (Ref fc x name) = Ref fc x name
embedSub sub (Meta fc x y xs)
    = Meta fc x y (map (embedSub sub) xs)
embedSub sub (Bind fc x b scope)
    = Bind fc x (map (embedSub sub) b) (embedSub (KeepCons sub) scope)
embedSub sub (App fc fn arg)
    = App fc (embedSub sub fn) (embedSub sub arg)
embedSub sub (As fc s nm pat)
    = As fc s (embedSub sub nm) (embedSub sub pat)
embedSub sub (TDelayed fc x y) = TDelayed fc x (embedSub sub y)
embedSub sub (TDelay fc x t y)
    = TDelay fc x (embedSub sub t) (embedSub sub y)
embedSub sub (TForce fc r x) = TForce fc r (embedSub sub x)
embedSub sub (PrimVal fc c) = PrimVal fc c
embedSub sub (Erased fc Impossible) = Erased fc Impossible
embedSub sub (Erased fc Placeholder) = Erased fc Placeholder
embedSub sub (Erased fc (Dotted t)) = Erased fc (Dotted (embedSub sub t))
embedSub sub (TType fc u) = TType fc u

namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

  export
  sizeOf : Bounds xs -> SizeOf xs
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export
addVars : SizeOf outer -> Bounds bound ->
          NVar name (outer ++ vars) ->
          NVar name (outer ++ (bound ++ vars))
addVars p = insertNVarNames p . sizeOf

resolveRef : SizeOf outer -> SizeOf done -> Bounds bound -> FC -> Name ->
             Maybe (Term (outer ++ (done ++ bound ++ vars)))
resolveRef p q None fc n = Nothing
resolveRef {outer} {done} p q (Add {xs} new old bs) fc n
    = if n == old
         then rewrite appendAssociative outer done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar (p + q) (MkNVar First) in
                     Just (Local fc Nothing _ p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef p (sucR q) bs fc n

mkLocals : SizeOf outer -> Bounds bound ->
           Term (outer ++ vars) -> Term (outer ++ (bound ++ vars))
mkLocals outer bs (Local fc r idx p)
    = let MkNVar p' = addVars outer bs (MkNVar p) in Local fc r _ p'
mkLocals outer bs (Ref fc Bound name)
    = maybe (Ref fc Bound name) id (resolveRef outer zero bs fc name)
mkLocals outer bs (Ref fc nt name)
    = Ref fc nt name
mkLocals outer bs (Meta fc name y xs)
    = maybe (Meta fc name y (map (mkLocals outer bs) xs))
            id (resolveRef outer zero bs fc name)
mkLocals outer bs (Bind fc x b scope)
    = Bind fc x (map (mkLocals outer bs) b)
           (mkLocals (suc outer) bs scope)
mkLocals outer bs (App fc fn arg)
    = App fc (mkLocals outer bs fn) (mkLocals outer bs arg)
mkLocals outer bs (As fc s as tm)
    = As fc s (mkLocals outer bs as) (mkLocals outer bs tm)
mkLocals outer bs (TDelayed fc x y)
    = TDelayed fc x (mkLocals outer bs y)
mkLocals outer bs (TDelay fc x t y)
    = TDelay fc x (mkLocals outer bs t) (mkLocals outer bs y)
mkLocals outer bs (TForce fc r x)
    = TForce fc r (mkLocals outer bs x)
mkLocals outer bs (PrimVal fc c) = PrimVal fc c
mkLocals outer bs (Erased fc Impossible) = Erased fc Impossible
mkLocals outer bs (Erased fc Placeholder) = Erased fc Placeholder
mkLocals outer bs (Erased fc (Dotted t)) = Erased fc (Dotted (mkLocals outer bs t))
mkLocals outer bs (TType fc u) = TType fc u

export
refsToLocals : Bounds bound -> Term vars -> Term (bound ++ vars)
refsToLocals None y = y
refsToLocals bs y = mkLocals zero  bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

export
isNVar : (n : Name) -> (ns : List Name) -> Maybe (NVar n ns)
isNVar n [] = Nothing
isNVar n (m :: ms)
    = case nameEq n m of
           Nothing   => map later (isNVar n ms)
           Just Refl => pure (MkNVar First)

export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Var ns)
isVar n ns = do
  MkNVar v <- isNVar n ns
  pure (MkVar v)

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : List Name) -> Term vars -> Term vars
resolveNames vars (Ref fc Bound name)
    = case isNVar name vars of
           Just (MkNVar prf) => Local fc (Just False) _ prf
           _ => Ref fc Bound name
resolveNames vars (Meta fc n i xs)
    = Meta fc n i (map (resolveNames vars) xs)
resolveNames vars (Bind fc x b scope)
    = Bind fc x (map (resolveNames vars) b) (resolveNames (x :: vars) scope)
resolveNames vars (App fc fn arg)
    = App fc (resolveNames vars fn) (resolveNames vars arg)
resolveNames vars (As fc s as pat)
    = As fc s (resolveNames vars as) (resolveNames vars pat)
resolveNames vars (TDelayed fc x y)
    = TDelayed fc x (resolveNames vars y)
resolveNames vars (TDelay fc x t y)
    = TDelay fc x (resolveNames vars t) (resolveNames vars y)
resolveNames vars (TForce fc r x)
    = TForce fc r (resolveNames vars x)
resolveNames vars tm = tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  public export
  data SubstEnv : List Name -> List Name -> Type where
       Nil : SubstEnv [] vars
       (::) : Term vars ->
              SubstEnv ds vars -> SubstEnv (d :: ds) vars

  findDrop : FC -> Maybe Bool ->
             Var (dropped ++ vars) ->
             SubstEnv dropped vars ->
             Term vars
  findDrop fc r (MkVar var) [] = Local fc r _ var
  findDrop fc r (MkVar First) (tm :: env) = tm
  findDrop fc r (MkVar (Later p)) (tm :: env)
      = findDrop fc r (MkVar p) env

  find : FC -> Maybe Bool ->
         SizeOf outer ->
         Var (outer ++ (dropped ++ vars)) ->
         SubstEnv dropped vars ->
         Term (outer ++ vars)
  find fc r outer var env = case sizedView outer of
    Z       => findDrop fc r var env
    S outer => case var of
      MkVar First     => Local fc r _ First
      MkVar (Later p) => weaken (find fc r outer (MkVar p) env)
       -- TODO: refactor to only weaken once?

  substEnv : SizeOf outer ->
             SubstEnv dropped vars ->
             Term (outer ++ (dropped ++ vars)) ->
             Term (outer ++ vars)
  substEnv outer env (Local fc r _ prf)
      = find fc r outer (MkVar prf) env
  substEnv outer env (Ref fc x name) = Ref fc x name
  substEnv outer env (Meta fc n i xs)
      = Meta fc n i (map (substEnv outer env) xs)
  substEnv outer env (Bind fc x b scope)
      = Bind fc x (map (substEnv outer env) b)
                  (substEnv (suc outer) env scope)
  substEnv outer env (App fc fn arg)
      = App fc (substEnv outer env fn) (substEnv outer env arg)
  substEnv outer env (As fc s as pat)
      = As fc s (substEnv outer env as) (substEnv outer env pat)
  substEnv outer env (TDelayed fc x y) = TDelayed fc x (substEnv outer env y)
  substEnv outer env (TDelay fc x t y)
      = TDelay fc x (substEnv outer env t) (substEnv outer env y)
  substEnv outer env (TForce fc r x) = TForce fc r (substEnv outer env x)
  substEnv outer env (PrimVal fc c) = PrimVal fc c
  substEnv outer env (Erased fc Impossible) = Erased fc Impossible
  substEnv outer env (Erased fc Placeholder) = Erased fc Placeholder
  substEnv outer env (Erased fc (Dotted t)) = Erased fc (Dotted (substEnv outer env t))
  substEnv outer env (TType fc u) = TType fc u

  export
  substs : SubstEnv dropped vars -> Term (dropped ++ vars) -> Term vars
  substs env tm = substEnv zero env tm

  export
  subst : Term vars -> Term (x :: vars) -> Term vars
  subst val tm = substs [val] tm

-- Replace an explicit name with a term
export
substName : Name -> Term vars -> Term vars -> Term vars
substName x new (Ref fc nt name)
    = case nameEq x name of
           Nothing => Ref fc nt name
           Just Refl => new
substName x new (Meta fc n i xs)
    = Meta fc n i (map (substName x new) xs)
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind fc y b scope)
    = Bind fc y (map (substName x new) b) (substName x (weaken new) scope)
substName x new (App fc fn arg)
    = App fc (substName x new fn) (substName x new arg)
substName x new (As fc s as pat)
    = As fc s as (substName x new pat)
substName x new (TDelayed fc y z)
    = TDelayed fc y (substName x new z)
substName x new (TDelay fc y t z)
    = TDelay fc y (substName x new t) (substName x new z)
substName x new (TForce fc r y)
    = TForce fc r (substName x new y)
substName x new tm = tm

export
addMetas : (usingResolved : Bool) -> NameMap Bool -> Term vars -> NameMap Bool
addMetas res ns (Local fc x idx y) = ns
addMetas res ns (Ref fc x name) = ns
addMetas res ns (Meta fc n i xs)
  = addMetaArgs (insert (ifThenElse res (Resolved i) n) False ns) xs
  where
    addMetaArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addMetaArgs ns [] = ns
    addMetaArgs ns (t :: ts) = addMetaArgs (addMetas res ns t) ts
addMetas res ns (Bind fc x (Let _ c val ty) scope)
    = addMetas res (addMetas res (addMetas res ns val) ty) scope
addMetas res ns (Bind fc x b scope)
    = addMetas res (addMetas res ns (binderType b)) scope
addMetas res ns (App fc fn arg)
    = addMetas res (addMetas res ns fn) arg
addMetas res ns (As fc s as tm) = addMetas res ns tm
addMetas res ns (TDelayed fc x y) = addMetas res ns y
addMetas res ns (TDelay fc x t y)
    = addMetas res (addMetas res ns t) y
addMetas res ns (TForce fc r x) = addMetas res ns x
addMetas res ns (PrimVal fc c) = ns
addMetas res ns (Erased fc i) = foldr (flip $ addMetas res) ns i
addMetas res ns (TType fc u) = ns

-- Get the metavariable names in a term
export
getMetas : Term vars -> NameMap Bool
getMetas tm = addMetas False empty tm

export
addRefs : (underAssert : Bool) -> (aTotal : Name) ->
          NameMap Bool -> Term vars -> NameMap Bool
addRefs ua at ns (Local fc x idx y) = ns
addRefs ua at ns (Ref fc x name) = insert name ua ns
addRefs ua at ns (Meta fc n i xs)
    = addRefsArgs ns xs
  where
    addRefsArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addRefsArgs ns [] = ns
    addRefsArgs ns (t :: ts) = addRefsArgs (addRefs ua at ns t) ts
addRefs ua at ns (Bind fc x (Let _ c val ty) scope)
    = addRefs ua at (addRefs ua at (addRefs ua at ns val) ty) scope
addRefs ua at ns (Bind fc x b scope)
    = addRefs ua at (addRefs ua at ns (binderType b)) scope
addRefs ua at ns (App _ (App _ (Ref fc _ name) x) y)
    = if name == at
         then addRefs True at (insert name True ns) y
         else addRefs ua at (addRefs ua at (insert name ua ns) x) y
addRefs ua at ns (App fc fn arg)
    = addRefs ua at (addRefs ua at ns fn) arg
addRefs ua at ns (As fc s as tm) = addRefs ua at ns tm
addRefs ua at ns (TDelayed fc x y) = addRefs ua at ns y
addRefs ua at ns (TDelay fc x t y)
    = addRefs ua at (addRefs ua at ns t) y
addRefs ua at ns (TForce fc r x) = addRefs ua at ns x
addRefs ua at ns (PrimVal fc c) = ns
addRefs ua at ns (Erased fc i) = foldr (flip $ addRefs ua at) ns i
addRefs ua at ns (TType fc u) = ns

-- As above, but for references. Also flag whether a name is under an
-- 'assert_total' because we may need to know that in coverage/totality
-- checking
export
getRefs : (aTotal : Name) -> Term vars -> NameMap Bool
getRefs at tm = addRefs False at empty tm


export
nameAt : {vars : _} -> {idx : Nat} -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} First     = n
nameAt {vars = n :: ns} (Later p) = nameAt p

export
withPiInfo : Show t => PiInfo t -> String -> String
withPiInfo Explicit tm = "(" ++ tm ++ ")"
withPiInfo Implicit tm = "{" ++ tm ++ "}"
withPiInfo AutoImplicit tm = "{auto " ++ tm ++ "}"
withPiInfo (DefImplicit t) tm = "{default " ++ show t ++ " " ++ tm ++ "}"


export
covering
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local _ c idx p) []
         = show (nameAt p) ++ "[" ++ show idx ++ "]"

      showApp (Ref _ _ n) [] = show n
      showApp (Meta _ n _ args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind _ x (Lam _ c info ty) sc) []
          = "\\" ++ withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
            " => " ++ show sc
      showApp (Bind _ x (Let _ c val ty) sc) []
          = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++
            " = " ++ show val ++ " in " ++ show sc
      showApp (Bind _ x (Pi _ c info ty) sc) []
          = withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
            " -> " ++ show sc
      showApp (Bind _ x (PVar _ c info ty) sc) []
          = withPiInfo info ("pat " ++ showCount c ++ show x ++ " : " ++ show ty) ++
            " => " ++ show sc
      showApp (Bind _ x (PLet _ c val ty) sc) []
          = "plet " ++ showCount c ++ show x ++ " : " ++ show ty ++
            " = " ++ show val ++ " in " ++ show sc
      showApp (Bind _ x (PVTy _ c ty) sc) []
          = "pty " ++ showCount c ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _ _) [] = "[can't happen]"
      showApp (As _ _ n tm) [] = show n ++ "@" ++ show tm
      showApp (TDelayed _ _ tm) [] = "%Delayed " ++ show tm
      showApp (TDelay _ _ _ tm) [] = "%Delay " ++ show tm
      showApp (TForce _ _ tm) [] = "%Force " ++ show tm
      showApp (PrimVal _ c) [] = show c
      showApp (Erased _ (Dotted t)) [] = ".(" ++ show t ++ ")"
      showApp (Erased _ _) [] = "[__]"
      showApp (TType _ u) [] = "Type"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
