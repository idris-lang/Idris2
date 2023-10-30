module Core.TT.Term

import Algebra

import Core.FC

import Core.Name
import Core.TT.Binder
import Core.TT.Var
import Core.TT.Primitive

import Data.List

%default total

------------------------------------------------------------------------
-- Name types
-- This information is cached in Refs (global variables) so as to avoid
-- too many lookups

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
data Term : SnocList Name -> Type where
     Local : FC -> (isLet : Maybe Bool) ->
             (idx : Nat) -> (0 p : IsVar name idx vars) -> Term vars
     Ref : FC -> NameType -> (name : Name) -> Term vars
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Int -> List (Term vars) -> Term vars
     Bind : FC -> (x : Name) ->
            (b : Binder (Term vars)) ->
            (scope : Term (vars :< x)) -> Term vars
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

export covering
StripNamespace (Term vars) where
  trimNS ns tm@(Ref fc x (NS tns n))
      = if ns == tns then Ref fc x (NS emptyNS n) else tm
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
