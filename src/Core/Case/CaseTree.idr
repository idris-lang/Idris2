module Core.Case.CaseTree

import Core.TT

import Idris.Pretty.Annotations

import Data.So
import Data.String

import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.Extra

%default covering

public export
data TCaseAlt : SnocList Name -> Type

||| Case trees in A-normal forms
||| i.e. we may only dispatch on variables, not expressions
public export
data CaseTree : Scoped where
       ||| case x return scTy of { p1 => e1 ; ... }
       TCase : {name : _} ->
              FC -> RigCount ->
              (idx : Nat) ->
              (0 p : IsVar name idx vars) ->
              (scTy : Term vars) -> List (TCaseAlt vars) ->
              CaseTree vars
       ||| TRHS: no need for further inspection
       ||| The Int is a clause id that allows us to see which of the
       ||| initial clauses are reached in the tree
       ||| Also record forced patterns (i.e. what we know variables are equal
       ||| to based on other matches)
       STerm : Int -> List (Var vars, Term vars) ->
               Term vars -> CaseTree vars
       ||| error from a partial match
       TUnmatched : FC -> (msg : String) -> CaseTree vars
       ||| Absurd context
       TImpossible : FC -> CaseTree vars

public export
data TCaseScope : SnocList Name -> Type where
  TRHS : CaseTree vars -> TCaseScope vars
  TArg : RigCount -> (x : Name) -> TCaseScope (vars :< x) -> TCaseScope vars

||| Case alternatives. Unlike arbitrary patterns, they can be at most
||| one constructor deep.
public export
data TCaseAlt : Scoped where
       ||| Constructor for a data type; bind the arguments and subterms.
       TConCase : FC -> Name -> (tag : Int) -> TCaseScope vars -> TCaseAlt vars
       ||| Lazy match for the Delay type use for codata types
       TDelayCase : FC -> (ty : Name) -> (arg : Name) ->
                   CaseTree (Scope.addInner vars [<ty, arg]) -> TCaseAlt vars
       ||| Match against a literal
       TConstCase : FC -> Constant -> CaseTree vars -> TCaseAlt vars
       ||| Catch-all case
       TDefaultCase : FC -> CaseTree vars -> TCaseAlt vars

export
FreelyEmbeddable CaseTree where

mutual
  export
  StripNamespace (CaseTree vars) where
    trimNS ns (TCase fc c idx p scTy xs)
        = TCase fc c idx p (trimNS ns scTy) (map (trimNS ns) xs)
    trimNS ns (STerm x fs t) = STerm x fs (trimNS ns t)
    trimNS ns c = c

    restoreNS ns (TCase fc c idx p scTy xs)
        = TCase fc c idx p (restoreNS ns scTy) (map (restoreNS ns) xs)
    restoreNS ns (STerm x fs t) = STerm x fs (restoreNS ns t)
    restoreNS ns c = c

  export
  StripNamespace (TCaseScope vars) where
    trimNS ns (TRHS ct) = TRHS (trimNS ns ct)
    trimNS ns (TArg ty arg t) = TArg ty arg (trimNS ns t)

    restoreNS ns (TRHS ct) = TRHS (restoreNS ns ct)
    restoreNS ns (TArg ty arg t) = TArg ty arg (restoreNS ns t)

  export
  StripNamespace (TCaseAlt vars) where
    trimNS ns (TConCase fc n t sc) = TConCase fc n t (trimNS ns sc)
    trimNS ns (TDelayCase fc ty arg t) = TDelayCase fc ty arg (trimNS ns t)
    trimNS ns (TConstCase fc x t) = TConstCase fc x (trimNS ns t)
    trimNS ns (TDefaultCase fc t) = TDefaultCase fc (trimNS ns t)

    restoreNS ns (TConCase fc n t sc) = TConCase fc n t (restoreNS ns sc)
    restoreNS ns (TDelayCase fc ty arg t) = TDelayCase fc ty arg (restoreNS ns t)
    restoreNS ns (TConstCase fc x t) = TConstCase fc x (restoreNS ns t)
    restoreNS ns (TDefaultCase fc t) = TDefaultCase fc (restoreNS ns t)


public export
data Pat : Type where
     PAs : FC -> Name -> Pat -> Pat
     PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
            SnocList (RigCount, Pat) -> Pat
     PTyCon : FC -> Name -> (arity : Nat) -> SnocList (RigCount, Pat) -> Pat
     PConst : FC -> (c : Constant) -> Pat
     PArrow : FC -> (x : Name) -> Pat -> Pat -> Pat
     PDelay : FC -> LazyReason -> Pat -> Pat -> Pat
     -- TODO: Matching on lazy types
     PLoc : FC -> Name -> Pat
     PUnmatchable : FC -> ClosedTerm -> Pat

export
isPConst : Pat -> Maybe Constant
isPConst (PConst _ c) = Just c
isPConst _ = Nothing

export
mkCaseAlt : CaseType -> TCaseAlt vars -> CaseAlt vars

export
mkTerm : CaseType -> CaseTree vars -> Term vars
mkTerm ct (TCase fc c idx p scTy xs)
   = Case fc ct c (Local fc  Nothing idx p) scTy (map (mkCaseAlt ct) xs)
mkTerm _ (STerm i _ tm) = tm
mkTerm _ (TUnmatched fc msg) = Unmatched fc msg
mkTerm _ (TImpossible fc) = Erased fc Impossible

mkCaseScope : CaseType -> TCaseScope vars -> CaseScope vars
mkCaseScope ct (TRHS (STerm _ fs tm)) = RHS fs tm
mkCaseScope ct (TRHS tm) = RHS [] (mkTerm ct tm)
mkCaseScope ct (TArg c x sc) = Arg c x (mkCaseScope ct sc)

mkCaseAlt ct (TConCase fc x tag sc) = ConCase fc x tag (mkCaseScope ct sc)
mkCaseAlt ct (TDelayCase fc ty arg tm) = DelayCase fc ty arg (mkTerm ct tm)
mkCaseAlt ct (TConstCase fc c tm) = ConstCase fc c (mkTerm ct tm)
mkCaseAlt ct (TDefaultCase fc tm) = DefaultCase fc (mkTerm ct tm)

public export
0 isConPat : Pat -> Bool
isConPat (PAs _ _ p) = isConPat p
isConPat (PCon {}) = True
isConPat (PTyCon {}) = True
isConPat (PConst {}) = True
isConPat (PArrow {}) = True
isConPat (PDelay {}) = True
isConPat _ = False

public export
0 IsConPat : Pat -> Type
IsConPat = So . isConPat

showCT : {vars : _} -> (indent : String) -> CaseTree vars -> String
showCA : {vars : _} -> (indent : String) -> TCaseAlt vars  -> String

showCT indent (TCase {name} _ _ idx prf ty alts)
  = "case " ++ show name ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of"
  ++ "\n" ++ indent ++ " { "
  ++ joinBy ("\n" ++ indent ++ " | ")
             (assert_total (map (showCA ("  " ++ indent)) alts))
  ++ "\n" ++ indent ++ " }"
showCT indent (STerm i fs tm)
  = "[" ++ show i ++ ": " ++ joinBy "," (map showForced fs) ++ "] " ++ show tm
  where
    showForced : (Var vars, Term vars) -> String
    showForced (MkVar v, tm) = show (Local EmptyFC Nothing _ v) ++ " = " ++ show tm
showCT indent (TUnmatched _ msg) = "Error: " ++ show msg
showCT indent (TImpossible _) = "Impossible"

showCA indent (TConCase _ n tag sc)
        = show n ++ " " ++ showScope sc
  where
    showScope : {vars : _} -> TCaseScope vars -> String
    showScope (TRHS tm) = " => " ++ showCT indent tm
    showScope (TArg c x sc) = show x ++ " " ++ showScope sc
showCA indent (TDelayCase _ _ arg sc)
        = "Delay " ++ show arg ++ " => " ++ showCT indent sc
showCA indent (TConstCase _ c sc)
        = "Constant " ++ show c ++ " => " ++ showCT indent sc
showCA indent (TDefaultCase _ sc)
        = "_ => " ++ showCT indent sc

export
{vars : _} -> Show (TCaseScope vars) where
    show (TRHS rhs) = " => rhs" --++ showCT "" rhs
    show (TArg r nm sc) = " " ++ show nm ++ show sc

export
covering
{vars : _} -> Show (CaseTree vars) where
  show = showCT ""

export
covering
{vars : _} -> Show (TCaseAlt vars) where
  show = showCA ""

mutual
  export
  eqTree : CaseTree vs -> CaseTree vs' -> Bool
  eqTree (TCase _ _ i _ _ alts) (TCase _ _ i' _ _ alts')
      = i == i'
       && length alts == length alts'
       && all (uncurry eqAlt) (zip alts alts')
  eqTree (STerm _ _ t) (STerm _ _ t') = eqTerm t t'
  eqTree (TUnmatched _ _) (TUnmatched _ _) = True
  eqTree (TImpossible _) (TImpossible _) = True
  eqTree _ _ = False

  eqScope : forall vs, vs' . TCaseScope vs -> TCaseScope vs' -> Bool
  eqScope (TRHS tm) (TRHS tm') = eqTree tm tm'
  eqScope (TArg _ _ sc) (TArg _ _ sc') = eqScope sc sc'
  eqScope _ _ = False

  eqAlt : TCaseAlt vs -> TCaseAlt vs' -> Bool
  eqAlt (TConCase _ n t sc) (TConCase _ n' t' sc')
      = n == n' && eqScope sc sc' -- assume arities match, since name does
  eqAlt (TDelayCase _ _ _ tree) (TDelayCase _ _ _ tree')
      = eqTree tree tree'
  eqAlt (TConstCase _ c tree) (TConstCase _ c' tree')
      = c == c' && eqTree tree tree'
  eqAlt (TDefaultCase _ tree) (TDefaultCase _ tree')
      = eqTree tree tree'
  eqAlt _ _ = False

export
covering
Show Pat where
  show (PAs _ n p) = show n ++ "@(" ++ show p ++ ")"
  show (PCon _ n i _ args) = show n ++ " " ++ show i ++ " " ++ assert_total (show $ toList args)
  show (PTyCon _ n _ args) = "<TyCon>" ++ show n ++ " " ++ assert_total (show $ toList args)
  show (PConst _ c) = show c
  show (PArrow _ x s t) = "(" ++ show s ++ " -> " ++ show t ++ ")"
  show (PDelay _ _ _ p) = "(Delay " ++ show p ++ ")"
  show (PLoc _ n) = show n
  show (PUnmatchable _ tm) = ".(" ++ show tm ++ ")"

export
Pretty IdrisSyntax Pat where
  prettyPrec d (PAs _ n p) = pretty0 n <++> keyword "@" <+> parens (pretty p)
  prettyPrec d (PCon _ n _ _ args) =
    parenthesise (d > Open) $ hsep (pretty0 n :: map (prettyPrec App . snd) (toList args))
  prettyPrec d (PTyCon _ n _ args) =
    parenthesise (d > Open) $ hsep (pretty0 n :: map (prettyPrec App . snd) (toList args))
  prettyPrec d (PConst _ c) = pretty c
  prettyPrec d (PArrow _ _ p q) =
    parenthesise (d > Open) $ pretty p <++> arrow <++> pretty q
  prettyPrec d (PDelay _ _ _ p) = parens ("Delay" <++> pretty p)
  prettyPrec d (PLoc _ n) = pretty0 n
  prettyPrec d (PUnmatchable _ tm) = keyword "." <+> parens (byShow tm)

mutual
  insertCaseNames : GenWeakenable CaseTree
  insertCaseNames mid inn (TCase fc c idx prf scTy alts)
      = let MkNVar prf' = insertNVarNames mid inn (MkNVar prf) in
            TCase fc c _ prf' (insertNames mid inn scTy)
                 (map (insertCaseAltNames mid inn) alts)
  insertCaseNames mid inn (STerm i vs x)
    = STerm i (map ( \(v, t) => (insertVarNames mid inn v,
                                 insertNames mid inn t)) vs)
              (insertNames mid inn x)
  insertCaseNames _ _ (TUnmatched fc msg) = TUnmatched fc msg
  insertCaseNames _ _ (TImpossible fc) = TImpossible fc

  insertCaseScopeNames : GenWeakenable TCaseScope
  insertCaseScopeNames mid inn (TRHS tm) = TRHS (insertCaseNames mid inn tm)
  insertCaseScopeNames mid inn (TArg c x sc)
      = TArg c x (insertCaseScopeNames mid (suc inn) sc)

  insertCaseAltNames : GenWeakenable TCaseAlt
  insertCaseAltNames mid inn (TConCase fc n t sc)
      = TConCase fc n t (insertCaseScopeNames mid inn sc)

  insertCaseAltNames mid inn (TDelayCase fc tyn valn ct)
      = TDelayCase fc tyn valn
                  (insertCaseNames mid (suc (suc inn)) ct)
  insertCaseAltNames mid inn (TConstCase fc x ct)
      = TConstCase fc x (insertCaseNames mid inn ct)
  insertCaseAltNames mid inn (TDefaultCase fc ct)
      = TDefaultCase fc (insertCaseNames mid inn ct)

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames ns zero t

export
Weaken TCaseScope where
  weakenNs ns t = insertCaseScopeNames ns zero t

total
getNames : (forall vs . NameMap Bool -> Term vs -> NameMap Bool) ->
           NameMap Bool -> CaseTree vars -> NameMap Bool
getNames add ns sc = getSet ns sc
  where
    mutual
      getAltSet : NameMap Bool -> TCaseAlt vs -> NameMap Bool
      getAltSet ns (TConCase _ n t sc) = getScope ns sc
      getAltSet ns (TDelayCase _ t a sc) = getSet ns sc
      getAltSet ns (TConstCase _ i sc) = getSet ns sc
      getAltSet ns (TDefaultCase _ sc) = getSet ns sc

      getScope : NameMap Bool -> TCaseScope vs -> NameMap Bool
      getScope ns (TRHS tm) = getSet ns tm
      getScope ns (TArg _ x sc) = getScope ns sc

      getAltSets : NameMap Bool -> List (TCaseAlt vs) -> NameMap Bool
      getAltSets ns [] = ns
      getAltSets ns (a :: as) = getAltSets (getAltSet ns a) as

      getSet : NameMap Bool -> CaseTree vs -> NameMap Bool
      getSet ns (TCase _ _ _ x ty []) = ns
      getSet ns (TCase _ _ _ x ty (a :: as)) = getAltSets (getAltSet ns a) as
      getSet ns (STerm _ _ tm) = add ns tm
      getSet ns (TUnmatched _ msg) = ns
      getSet ns (TImpossible _) = ns

namespace Pattern
  export
  mkTerm : (vars : Scope) -> Pat -> Term vars
  mkTerm vars (PAs fc x y) = mkTerm vars y
  mkTerm vars (PCon fc x tag arity xs)
      = applySpine fc (Ref fc (DataCon tag arity) x)
                      (map @{Compose} (mkTerm vars) xs)
  mkTerm vars (PTyCon fc x arity xs)
      = applySpine fc (Ref fc (TyCon arity) x)
                      (map @{Compose} (mkTerm vars) xs)
  mkTerm vars (PConst fc c) = PrimVal fc c
  mkTerm vars (PArrow fc x s t)
      = Bind fc x (Pi fc top Explicit (mkTerm vars s)) (mkTerm (Scope.bind vars x) t)
  mkTerm vars (PDelay fc r ty p)
      = TDelay fc r (mkTerm vars ty) (mkTerm vars p)
  mkTerm vars (PLoc fc n)
      = case isVar n vars of
            Just (MkVar prf) => Local fc Nothing _ prf
            _ => Ref fc Bound n
  mkTerm vars (PUnmatchable fc tm) = embed tm
