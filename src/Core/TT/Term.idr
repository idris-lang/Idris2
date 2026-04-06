module Core.TT.Term

import Algebra

import Core.FC
import Core.Name.Scoped
import Core.Name.CompatibleVars
import Core.TT.Binder
import Core.TT.Primitive
import Core.TT.Var

import Data.String
import Data.Vect

import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.LengthMatch

%default total

------------------------------------------------------------------------
-- Name types
-- This information is cached in Refs (global variables) so as to avoid
-- too many lookups

public export
Tag : Type
Tag = Int

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Tag) -> (arity : Nat) -> NameType
     TyCon   : (arity : Nat) -> NameType

%name NameType nt

export
covering
Show NameType where
  showPrec d Bound = "Bound"
  showPrec d Func = "Func"
  showPrec d (DataCon tag ar) = showCon d "DataCon" $ showArg tag ++ showArg ar
  showPrec d (TyCon ar) = showCon d "TyCon" $ showArg ar

export
isCon : NameType -> Maybe Nat
isCon (DataCon t a) = Just a
isCon (TyCon a) = Just a
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

export
Show UseSide where
  show UseLeft = "UseLeft"
  show UseRight = "UseRight"

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

-- A 'Case' arises either from a top level pattern match, or a 'case' block,
-- and it's useful to know the difference so we know when to stop reducing due
-- to a blocked top level function
public export
data CaseType = PatMatch | CaseBlock Name

export
Show CaseType where
  show PatMatch = "(pat)"
  show (CaseBlock n) = "(block " ++ show n ++ ")"

------------------------------------------------------------------------
-- Core Terms

public export
data CaseAlt : SnocList Name -> Type

public export
data Term : Scoped where
     Local : FC -> (isLet : Maybe Bool) ->
             (idx : Nat) -> (0 p : IsVar name idx vars) -> Term vars
     Ref : FC -> NameType -> (name : Name) -> Term vars
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Int -> List (RigCount, Term vars) -> Term vars
     Bind : FC -> (x : Name) ->
            (b : Binder (Term vars)) ->
            (scope : Term (Scope.bind vars x)) -> Term vars
     App : FC -> (fn : Term vars) -> RigCount -> (arg : Term vars) -> Term vars
     -- as patterns; since we check LHS patterns as terms before turning
     -- them into patterns, this helps us get it right. When normalising,
     -- we just reduce the inner term and ignore the 'as' part
     -- The 'as' part should really be a Name rather than a Term, but it's
     -- easier this way since it gives us the ability to work with unresolved
     -- names (Ref) and resolved names (Local) without having to define a
     -- special purpose thing. (But it'd be nice to tidy that up, nevertheless)
     As : FC -> UseSide -> (as : Term vars) -> (pat : Term vars) -> Term vars
     Case : FC -> CaseType ->
            RigCount -> (sc : Term vars) -> (scTy : Term vars) ->
            List (CaseAlt vars) ->
            Term vars
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vars -> Term vars
     TDelay : FC -> LazyReason -> (ty : Term vars) -> (arg : Term vars) -> Term vars
     TForce : FC -> LazyReason -> Term vars -> Term vars
     PrimVal : FC -> (c : Constant) -> Term vars
     PrimOp : {arity : _} ->
              FC -> PrimFn arity -> Vect arity (Term vars) -> Term vars
     Erased : FC -> WhyErased (Term vars) -> Term vars
     Unmatched : FC -> String -> Term vars -- error from a partialmatch
     TType : FC -> Name -> -- universe variable
             Term vars

%name Term t, u

public export
ClosedTerm : Type
ClosedTerm = Term Scope.empty

public export
data CaseScope : Scope -> Type where
     RHS : List (Var vars, Term vars) -> -- Forced equalities
           Term vars -> -- RHS
           CaseScope vars
     Arg : RigCount -> (x : Name) -> CaseScope (vars :< x) -> CaseScope vars

||| Case alternatives. Unlike arbitrary patterns, they can be at most
||| one constructor deep.
public export
data CaseAlt : Scoped where
     ||| Constructor for a data type; bind the arguments and subterms.
     ConCase : FC -> Name -> (tag : Int) -> CaseScope vars -> CaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     DelayCase : FC -> (ty : Name) -> (arg : Name) ->
                 Term (vars :< ty :< arg) -> CaseAlt vars
     ||| Match against a literal
     ConstCase : FC -> Constant -> Term vars -> CaseAlt vars
     ||| Catch-all case
     DefaultCase : FC -> Term vars -> CaseAlt vars

export
isDefault : CaseAlt vars -> Bool
isDefault (DefaultCase _ _) = True
isDefault _ = False

------------------------------------------------------------------------
-- Weakening
insertNamesAlt : GenWeakenable CaseAlt

export
insertNames : GenWeakenable Term
insertNames mid inn (Local fc r idx prf)
   = let MkNVar prf' = insertNVarNames mid inn (MkNVar prf) in
     Local fc r _ prf'
insertNames mid inn (Ref fc nt name) = Ref fc nt name
insertNames mid inn (Meta fc name idx args)
    = Meta fc name idx (assert_total $ map @{Compose} (insertNames mid inn) args)
insertNames mid inn (Bind fc x b scope)
    = Bind fc x (assert_total (map (insertNames mid inn) b))
           (insertNames mid (suc inn) scope)
insertNames mid inn (App fc fn c arg)
    = App fc (insertNames mid inn fn) c (insertNames mid inn arg)
insertNames mid inn (As fc s as tm)
    = As fc s (insertNames mid inn as) (insertNames mid inn tm)
insertNames out ns (Case fc t r sc scTy xs)
    = Case fc t r (insertNames out ns sc) (insertNames out ns scTy)
           (assert_total $ map (insertNamesAlt out ns) xs)
insertNames mid inn (TDelayed fc r ty) = TDelayed fc r (insertNames mid inn ty)
insertNames mid inn (TDelay fc r ty tm)
    = TDelay fc r (insertNames mid inn ty) (insertNames mid inn tm)
insertNames mid inn (TForce fc r tm) = TForce fc r (insertNames mid inn tm)
insertNames mid inn (PrimVal fc c) = PrimVal fc c
insertNames out ns (PrimOp fc x xs)
    = PrimOp fc x (assert_total (map (insertNames out ns) xs))
insertNames mid inn (Erased fc Impossible) = Erased fc Impossible
insertNames mid inn (Erased fc Placeholder) = Erased fc Placeholder
insertNames mid inn (Erased fc (Dotted t)) = Erased fc (Dotted (insertNames mid inn t))
insertNames out ns (Unmatched fc x) = Unmatched fc x
insertNames mid inn (TType fc u) = TType fc u

insertNamesScope : GenWeakenable CaseScope
insertNamesScope out ns (RHS fs tm)
    = RHS (map (\ (n, tm) => (insertVarNames out ns n,
                              insertNames out ns tm)) fs)
          (insertNames out ns tm)
insertNamesScope out ns (Arg r x sc) = Arg r x (insertNamesScope out (suc ns) sc)

insertNamesAlt out sns (ConCase fc n t scope)
    = ConCase fc n t (insertNamesScope out sns scope)
insertNamesAlt out ns (DelayCase fc ty arg scope)
    = DelayCase fc ty arg (insertNames out (suc (suc ns)) scope)
insertNamesAlt out ns (ConstCase fc c scope)
    = ConstCase fc c (insertNames out ns scope)
insertNamesAlt out ns (DefaultCase fc scope)
    = DefaultCase fc (insertNames out ns scope)

export
compatTerm : CompatibleVars xs ys -> Term xs -> Term ys
compatTerm compat tm = believe_me tm -- no names in term, so it's identity
-- This is how we would define it:
-- compatTerm CompatPre tm = tm
-- compatTerm prf (Local fc r idx vprf)
--     = let MkVar vprf' = compatIsVar prf vprf in
--           Local fc r _ vprf'
-- compatTerm prf (Ref fc x name) = Ref fc x name
-- compatTerm prf (Meta fc n i args)
--     = Meta fc n i (map (compatTerm prf) args)
-- compatTerm prf (Bind fc x b scope)
--     = Bind fc x (map (compatTerm prf) b) (compatTerm (CompatExt prf) scope)
-- compatTerm prf (App fc fn c arg)
--     = App fc (compatTerm prf fn) c (compatTerm prf arg)
-- compatTerm prf (As fc s as tm)
--     = As fc s (compatTerm prf as) (compatTerm prf tm)
-- compatTerm prf (TDelayed fc r ty) = TDelayed fc r (compatTerm prf ty)
-- compatTerm prf (TDelay fc r ty tm)
--     = TDelay fc r (compatTerm prf ty) (compatTerm prf tm)
-- compatTerm prf (TForce fc r x) = TForce fc r (compatTerm prf x)
-- compatTerm prf (PrimVal fc c) = PrimVal fc c
-- compatTerm prf (Erased fc i) = Erased fc i
-- compatTerm prf (TType fc) = TType fc

export
shrinkTerm : Shrinkable Term

export
shrinkPi : Shrinkable (PiInfo . Term)
shrinkPi pinfo th
  = assert_total
  $ traverse (\ t => shrinkTerm t th) pinfo

export
shrinkBinder : Shrinkable (Binder . Term)
shrinkBinder binder th
  = assert_total
  $ traverse (\ t => shrinkTerm t th) binder

export
shrinkTerms : Shrinkable (List . Term)
shrinkTerms ts th
  = assert_total
  $ traverse (\ t => shrinkTerm t th) ts

export
shrinkTaggedTerms : Shrinkable (List . (RigCount,) . Term)
shrinkTaggedTerms ts th
  = assert_total
  $ traverse @{Compose} (\ t => shrinkTerm t th) ts

shrinkScope : Shrinkable CaseScope
shrinkScope (RHS fs tm) prf
    = Just (RHS !(traverse shrinkForcedEq fs) !(shrinkTerm tm prf))
  where
    shrinkForcedEq : (Var xs, Term xs) -> Maybe (Var ys, Term ys)
    shrinkForcedEq (MkVar v, tm) = Just (!(shrinkIsVar v prf), !(shrinkTerm tm prf))
shrinkScope (Arg r x sc) prf = Just (Arg r x !(shrinkScope sc (Keep prf)))

shrinkAlt : Shrinkable CaseAlt
shrinkAlt (ConCase fc x tag sc) prf
  = ConCase fc x tag <$> shrinkScope sc prf
shrinkAlt (DelayCase fc ty arg sc) prf
  = DelayCase fc ty arg <$> shrinkTerm sc (Keep (Keep prf))
shrinkAlt (ConstCase fc c sc) prf = ConstCase fc c <$> shrinkTerm sc prf
shrinkAlt (DefaultCase fc sc) prf = DefaultCase fc <$> shrinkTerm sc prf

shrinkTerm (Local fc r idx loc) prf
  = do MkVar loc' <- shrinkIsVar loc prf
       pure (Local fc r _ loc')
shrinkTerm (Ref fc x name) prf = Just (Ref fc x name)
shrinkTerm (Meta fc x y xs) prf
    = do Just (Meta fc x y !(shrinkTaggedTerms xs prf))
shrinkTerm (Bind fc x b scope) prf
    = Just (Bind fc x !(shrinkBinder b prf) !(shrinkTerm scope (Keep prf)))
shrinkTerm (App fc fn c arg) prf
    = Just (App fc !(shrinkTerm fn prf) c !(shrinkTerm arg prf))
shrinkTerm (As fc s as tm) prf
    = Just (As fc s !(shrinkTerm as prf) !(shrinkTerm tm prf))
shrinkTerm (Case fc t r sc scTy alts) prf
   = Just (Case fc t r !(shrinkTerm sc prf) !(shrinkTerm scTy prf)
                !(assert_total $ traverse (\alt => shrinkAlt alt prf) alts))
shrinkTerm (TDelayed fc x y) prf
    = Just (TDelayed fc x !(shrinkTerm y prf))
shrinkTerm (TDelay fc x t y) prf
    = Just (TDelay fc x !(shrinkTerm t prf) !(shrinkTerm y prf))
shrinkTerm (TForce fc r x) prf
    = Just (TForce fc r !(shrinkTerm x prf))
shrinkTerm (PrimVal fc c) prf = Just (PrimVal fc c)
shrinkTerm (PrimOp fc fn args) prf
    = Just (PrimOp fc fn !(assert_total $ (traverse (\arg => shrinkTerm arg prf) args)))
shrinkTerm (Erased fc Placeholder) prf = Just (Erased fc Placeholder)
shrinkTerm (Erased fc Impossible) prf = Just (Erased fc Impossible)
shrinkTerm (Erased fc (Dotted t)) prf = Erased fc . Dotted <$> shrinkTerm t prf
shrinkTerm (Unmatched fc s) prf = Just (Unmatched fc s)
shrinkTerm (TType fc u) prf = Just (TType fc u)


thinTerm : Thinnable Term

export
thinPi : Thinnable (PiInfo . Term)
thinPi pinfo th = assert_total $ map (\ t => thinTerm t th) pinfo

export
thinBinder : Thinnable (Binder . Term)
thinBinder binder th = assert_total $ map (\ t => thinTerm t th) binder

export
thinTerms : Thinnable (List . Term)
thinTerms ts th = assert_total $ map (\ t => thinTerm t th) ts

export
thinVect : forall a. Thinnable (Vect a . Term)
thinVect ts th = assert_total $ map (\ t => thinTerm t th) ts

export
thinTaggedTerms : Thinnable (List . (RigCount,) . Term)
thinTaggedTerms ts th = assert_total $ map @{Compose} (\ t => thinTerm t th) ts

thinScope : Thinnable CaseScope
thinScope (RHS fs tm) th
  = RHS (thinForcedEq <$> fs) (thinTerm tm th)
  where
    thinForcedEq : (Var xs, Term xs) -> (Var ys, Term ys)
    thinForcedEq (MkVar v, tm) = (thinIsVar v th, thinTerm tm th)
thinScope (Arg r x sc) prf = Arg r x (thinScope sc (Keep prf))

thinAlt : Thinnable CaseAlt
thinAlt (ConCase fc n t sc) th = ConCase fc n t (thinScope sc th)
thinAlt (DelayCase fc t a tm) th = DelayCase fc t a (thinTerm tm (Keep (Keep th)))
thinAlt (ConstCase fc c tm) th = ConstCase fc c (thinTerm tm th)
thinAlt (DefaultCase fc tm) th = DefaultCase fc (thinTerm tm th)

thinAlts : Thinnable (List . CaseAlt)
thinAlts alts th = assert_total $ map (\ t => thinAlt t th) alts

thinTerm (Local fc x idx y) th
    = let MkVar y' = thinIsVar y th in Local fc x _ y'
thinTerm (Ref fc x name) th = Ref fc x name
thinTerm (Meta fc x y xs) th
    = Meta fc x y (thinTaggedTerms xs th)
thinTerm (Bind fc x b scope) th
    = Bind fc x (thinBinder b th) (thinTerm scope (Keep th))
thinTerm (App fc fn c arg) th
    = App fc (thinTerm fn th) c (thinTerm arg th)
thinTerm (As fc s nm pat) th
    = As fc s (thinTerm nm th) (thinTerm pat th)
thinTerm (TDelayed fc x y) th = TDelayed fc x (thinTerm y th)
thinTerm (TDelay fc x t y) th
    = TDelay fc x (thinTerm t th) (thinTerm y th)
thinTerm (Case fc t r sc scTy alts) th
   = Case fc t r (thinTerm sc th) (thinTerm scTy th) (thinAlts alts th)
thinTerm (TForce fc r x) th = TForce fc r (thinTerm x th)
thinTerm (PrimVal fc c) th = PrimVal fc c
thinTerm (PrimOp fc x args) th
    = PrimOp fc x (thinVect args th)
thinTerm (Erased fc Impossible) th = Erased fc Impossible
thinTerm (Erased fc Placeholder) th = Erased fc Placeholder
thinTerm (Erased fc (Dotted t)) th = Erased fc (Dotted (thinTerm t th))
thinTerm (Unmatched fc s) th = Unmatched fc s
thinTerm (TType fc u) th = TType fc u

export
GenWeaken Term where
  genWeakenNs = assert_total $ insertNames

export
%hint
WeakenTerm : Weaken Term
WeakenTerm = GenWeakenWeakens

export
FreelyEmbeddable Term where

export
IsScoped Term where
  shrink = shrinkTerm
  thin = thinTerm
  compatNs = compatTerm

------------------------------------------------------------------------
-- Smart constructors

export
apply : FC -> Term vars -> List (RigCount, Term vars) -> Term vars
apply loc fn [] = fn
apply loc fn ((c, a) :: args) = apply loc (App loc fn c a) args

export
applySpine : FC -> Term vars -> SnocList (RigCount, Term vars) -> Term vars
applySpine loc fn [<] = fn
applySpine loc fn (args :< (c, a)) = App loc (applySpine loc fn args) c a

-- Creates a chain of `App` nodes, each with its own file context
export
applySpineWithFC : Term vars -> SnocList (FC, RigCount, Term vars) -> Term vars
applySpineWithFC fn [<] = fn
applySpineWithFC fn (args :< (fc, c, arg)) = App fc (applySpineWithFC fn args) c arg

-- Creates a chain of `App` nodes, each with its own file context
export
applyStackWithFC : Term vars -> List (FC, RigCount, Term vars) -> Term vars
applyStackWithFC fn [] = fn
applyStackWithFC fn ((fc, c, arg) :: args) = applyStackWithFC (App fc fn c arg) args

-- Build a simple function type
export
fnType : FC -> Term vars -> Term vars -> Term vars
fnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc top Explicit arg) (weaken scope)

export
linFnType : FC -> Term vars -> Term vars -> Term vars
linFnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc linear Explicit arg) (weaken scope)

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App _ f _ a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFnArgsWithCounts : Term vars -> (Term vars, List (RigCount, Term vars))
getFnArgsWithCounts tm = getFA [] tm
  where
    getFA : List (RigCount, Term vars) -> Term vars ->
            (Term vars, List (RigCount, Term vars))
    getFA args (App _ f c a) = getFA ((c, a) :: args) f
    getFA args tm = (tm, args)

export
getFnArgsSpine : Term vars -> (Term vars, SnocList (RigCount, Term vars))
getFnArgsSpine (App _ f c a)
    = let (fn, sp) = getFnArgsSpine f in
          (fn, sp :< (c, a))
getFnArgsSpine tm = (tm, [<])

export
getFn : Term vars -> Term vars
getFn (App _ f _ a) = getFn f
getFn tm = tm

export
getArgs : Term vars -> (List (Term vars))
getArgs = snd . getFnArgs

export
varExtend : IsVar x idx xs -> IsVar x idx (ys ++ xs)
-- What Could Possibly Go Wrong?
-- This relies on the runtime representation of the term being the same
-- after embedding! It is just an identity function at run time, though, and
-- we don't need its definition at compile time, so let's do it...
varExtend p = believe_me p

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars compat tm = believe_me tm -- no names in term, so it's identity

export
renameNTopVar : (ms : SnocList Name) ->
             LengthMatch ns ms ->
             Var (vars ++ ns) -> Var (vars ++ ms)
renameNTopVar ms ok v = believe_me v

export
renameNTop : (ms : SnocList Name) ->
             LengthMatch ns ms ->
             Term (vars ++ ns) -> Term (vars ++ ms)
renameNTop ms ok tm = believe_me tm

export
renameTop : (m : Name) -> Term (vars :< n) -> Term (vars :< m)
renameTop m tm = renameNTop {ns = [<n]} [<m] (SnocMatch LinMatch) tm

------------------------------------------------------------------------
-- Namespace manipulations

-- Remove/restore the given namespace from all Refs. This is to allow
-- writing terms and case trees to disk without repeating the same namespace
-- all over the place.
public export
interface StripNamespace a where
  trimNS : Namespace -> a -> a
  restoreNS : Namespace -> a -> a

export
StripNamespace a => StripNamespace (Maybe a) where
  trimNS ns Nothing = Nothing
  trimNS ns (Just x) = Just (trimNS ns x)
  restoreNS ns Nothing = Nothing
  restoreNS ns (Just x) = Just (restoreNS ns x)

export
StripNamespace a => StripNamespace (List a) where
  trimNS c ns = trimNS_aux c [] ns
    where trimNS_aux : Namespace -> List a -> List a -> List a
          trimNS_aux c res [] = reverse res
          trimNS_aux c res (n :: ns) = trimNS_aux c ((trimNS c n):: res) ns


  restoreNS c ns = restoreNS_aux c [] ns
    where restoreNS_aux : Namespace -> List a -> List a -> List a
          restoreNS_aux c res [] = reverse res
          restoreNS_aux c res (n :: ns) = restoreNS_aux c ((restoreNS c n) :: res) ns

export
StripNamespace Name where
  trimNS ns nm@(NS tns n)
    = if ns == tns then NS emptyNS n else nm
      -- ^ A blank namespace, rather than a UN, so we don't catch primitive
      -- names which are represented as UN.
  trimNS ns nm = nm

  restoreNS ns nm@(NS tns n)
      = if isNil (unsafeUnfoldNamespace tns)
            then NS ns n
            else nm
  restoreNS ns nm = nm

export covering
StripNamespace (Term vars) where
  trimNS ns (Ref fc x nm)
      = Ref fc x (trimNS ns nm)
  trimNS ns (Meta fc x y xs)
      = Meta fc x y (map @{Compose} (trimNS ns) xs)
  trimNS ns (Bind fc x b scope)
      = Bind fc x (map (trimNS ns) b) (trimNS ns scope)
  trimNS ns (App fc fn c arg)
      = App fc (trimNS ns fn) c (trimNS ns arg)
  trimNS ns (As fc s p tm)
      = As fc s (trimNS ns p) (trimNS ns tm)
  trimNS ns (TDelayed fc x y)
      = TDelayed fc x (trimNS ns y)
  trimNS ns (TDelay fc x t y)
      = TDelay fc x (trimNS ns t) (trimNS ns y)
  trimNS ns (TForce fc r y)
      = TForce fc r (trimNS ns y)
  trimNS ns tm = tm

  restoreNS ns (Ref fc x nm)
      = Ref fc x (restoreNS ns nm)
  restoreNS ns (Meta fc x y xs)
      = Meta fc x y (map @{Compose} (restoreNS ns) xs)
  restoreNS ns (Bind fc x b scope)
      = Bind fc x (map (restoreNS ns) b) (restoreNS ns scope)
  restoreNS ns (App fc fn c arg)
      = App fc (restoreNS ns fn) c (restoreNS ns arg)
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
isErased (Erased {}) = True
isErased _ = False

export
getLoc : Term vars -> FC
getLoc (Local fc _ _ _) = fc
getLoc (Ref fc _ _) = fc
getLoc (Meta fc _ _ _) = fc
getLoc (Bind fc _ _ _) = fc
getLoc (App fc _ _ _) = fc
getLoc (As fc _ _ _) = fc
getLoc (Case fc _ _ _ _ _) = fc
getLoc (TDelayed fc _ _) = fc
getLoc (TDelay fc _ _ _) = fc
getLoc (TForce fc _ _) = fc
getLoc (PrimVal fc _) = fc
getLoc (PrimOp fc _ _) = fc
getLoc (Erased fc i) = fc
getLoc (Unmatched fc _) = fc
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
total
Eq a => Eq (WhyErased a) where
  Placeholder == Placeholder = True
  Impossible == Impossible = True
  Dotted t == Dotted u = t == u
  _ == _ = False

export
eqWhyErasedBy : (a -> b -> Bool) -> WhyErased a -> WhyErased b -> Bool
eqWhyErasedBy eq Impossible Impossible = True
eqWhyErasedBy eq Placeholder Placeholder = True
eqWhyErasedBy eq (Dotted t) (Dotted u) = eq t u
eqWhyErasedBy eq _ _ = False

export
total
eqTerm : Term vs -> Term vs' -> Bool
eqTerm (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
eqTerm (Ref _ _ n) (Ref _ _ n') = n == n'
eqTerm (Meta _ _ i args) (Meta _ _ i' args')
    = i == i' && assert_total (all (uncurry eqTerm) (zip (map snd args) (map snd args')))
eqTerm (Bind _ _ b sc) (Bind _ _ b' sc')
    = assert_total (eqBinderBy eqTerm b b') && eqTerm sc sc'
eqTerm (App _ f _ a) (App _ f' _ a') = eqTerm f f' && eqTerm a a'
eqTerm (As _ _ a p) (As _ _ a' p') = eqTerm a a' && eqTerm p p'
eqTerm (Case _ _ _ sc ty alts) (Case _ _ _ sc' ty' alts')
    = eqTerm sc sc' && eqTerm ty ty' &&
          assert_total (all (uncurry eqAlt) (zip alts alts'))
  where
    eqScope : forall vs, vs' . CaseScope vs -> CaseScope vs' -> Bool
    eqScope (RHS _ tm) (RHS _ tm') = eqTerm tm tm'
    eqScope (Arg _ _ sc) (Arg _ _ sc') = eqScope sc sc'
    eqScope _ _ = False

    eqAlt : CaseAlt vs -> CaseAlt vs' -> Bool
    eqAlt (ConCase _ n tag sc) (ConCase _ n' tag' sc') = tag == tag' && eqScope sc sc'
    eqAlt (DelayCase _ ty arg tm) (DelayCase _ ty' arg' tm') = eqTerm tm tm'
    eqAlt (ConstCase _ c tm) (ConstCase _ c' tm') = c == c' && eqTerm tm tm'
    eqAlt (DefaultCase _ tm) (DefaultCase _ tm') = eqTerm tm tm'
    eqAlt _ _ = False
eqTerm (TDelayed _ _ t) (TDelayed _ _ t') = eqTerm t t'
eqTerm (TDelay _ _ t x) (TDelay _ _ t' x') = eqTerm t t' && eqTerm x x'
eqTerm (TForce _ _ t) (TForce _ _ t') = eqTerm t t'
eqTerm (PrimVal _ c) (PrimVal _ c') = c == c'
eqTerm (Erased _ i) (Erased _ i') = assert_total (eqWhyErasedBy eqTerm i i')
eqTerm (TType {}) (TType {}) = True
eqTerm _ _ = False

export
total
Eq (Term vars) where
  (==) = eqTerm

------------------------------------------------------------------------
-- Scope checking

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : Scope) -> Term vars -> Term vars

resolveNamesBinder : (vars : Scope) -> Binder (Term vars) -> Binder (Term vars)
resolveNamesBinder vars b = assert_total $ map (resolveNames vars) b

resolveNamesTerms : (vars : Scope) -> List (RigCount, Term vars) -> List (RigCount, Term vars)
resolveNamesTerms vars ts = assert_total $ map @{Compose} (resolveNames vars) ts

resolveScope : (vars : SnocList Name) -> CaseScope vars -> CaseScope vars
resolveScope vars (RHS fs tm)
    = RHS (map (\ (n, t) => (n, resolveNames vars t)) fs)
          (resolveNames vars tm)
resolveScope vars (Arg c x sc) = Arg c x (resolveScope (vars :< x) sc)

resolveAlt : (vars : SnocList Name) -> CaseAlt vars -> CaseAlt vars
resolveAlt vars (ConCase fc x tag sc)
    = ConCase fc x tag (resolveScope vars sc)
resolveAlt vars (DelayCase fc ty arg tm)
    = DelayCase fc ty arg (resolveNames (vars :< ty :< arg) tm)
resolveAlt vars (ConstCase fc x tm) = ConstCase fc x (resolveNames vars tm)
resolveAlt vars (DefaultCase fc tm) = DefaultCase fc (resolveNames vars tm)

resolveNames vars (Ref fc Bound name)
    = case isNVar name vars of
            Just (MkNVar prf) => Local fc (Just False) _ prf
            _ => Ref fc Bound name
resolveNames vars (Meta fc n i xs)
    = Meta fc n i (resolveNamesTerms vars xs)
resolveNames vars (Bind fc x b scope)
    = Bind fc x (resolveNamesBinder vars b) (resolveNames (Scope.bind vars x) scope)
resolveNames vars (App fc fn c arg)
    = App fc (resolveNames vars fn) c (resolveNames vars arg)
resolveNames vars (As fc s as pat)
    = As fc s (resolveNames vars as) (resolveNames vars pat)
resolveNames vars (Case fc t c sc scty alts)
    = Case fc t c (resolveNames vars sc) (resolveNames vars scty)
                  (map (assert_total $ resolveAlt vars) alts)
resolveNames vars (TDelayed fc x y)
    = TDelayed fc x (resolveNames vars y)
resolveNames vars (TDelay fc x t y)
    = TDelay fc x (resolveNames vars t) (resolveNames vars y)
resolveNames vars (TForce fc r x)
    = TForce fc r (resolveNames vars x)
resolveNames vars tm = tm

------------------------------------------------------------------------
-- Showing

export
withPiInfo : Show t => PiInfo t -> String -> String
withPiInfo Explicit tm = "(" ++ tm ++ ")"
withPiInfo Implicit tm = "{" ++ tm ++ "}"
withPiInfo AutoImplicit tm = "{auto " ++ tm ++ "}"
withPiInfo (DefImplicit t) tm = "{default " ++ show t ++ " " ++ tm ++ "}"

export
{vars : _} -> Show (Term vars)

export
covering
{vars : _} -> Show (CaseScope vars) where
    show (RHS fs rhs) = " => " ++ show fs ++ " " ++ show rhs
    show (Arg r nm sc) = " " ++ show nm ++ show sc

export
covering
{vars : _} -> Show (CaseAlt vars) where
   show (ConCase _ n t sc) = show n ++ show sc
   show (DelayCase _ ty arg sc) = "Delay " ++ show arg ++ " => " ++ show sc
   show (ConstCase _ c sc) = show c ++ " => " ++ show sc
   show (DefaultCase _ sc) = "_ => " ++ show sc

export
covering
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgsWithCounts tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (ZeroOneOmega, Term vars) -> String
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
      showApp (App _ {}) [] = "[can't happen]"
      showApp (As _ _ n tm) [] = show n ++ "@" ++ show tm
      showApp (Case _ t r sc scty alts) []
            = "case " ++ show r ++ " " ++ show sc ++ " : " ++ show scty ++ " of " ++ show alts
      showApp (TDelayed _ _ tm) [] = "%Delayed " ++ show tm
      showApp (TDelay _ _ _ tm) [] = "%Delay " ++ show tm
      showApp (TForce _ _ tm) [] = "%Force " ++ show tm
      showApp (PrimVal _ c) [] = show c
      showApp (PrimOp _ f ar) [] = "PrimOp " ++ show f ++ " " ++ show (length ar)
      showApp (Erased _ (Dotted t)) [] = ".(" ++ show t ++ ")"
      showApp (Erased {}) [] = "[__]"
      showApp (TType _ u) [] = "Type"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (joinBy " " (map show args))
                     ++ ")"
