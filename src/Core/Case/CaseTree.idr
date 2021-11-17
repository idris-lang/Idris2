module Core.Case.CaseTree

import Core.TT

import Data.Bool
import Data.List

import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter

%default covering

mutual
  ||| Case trees in A-normal forms
  ||| i.e. we may only dispatch on variables, not expressions
  public export
  data CaseTree : List Name -> Type where
       ||| case x return scTy of { p1 => e1 ; ... }
       Case : {name : _} ->
              (idx : Nat) ->
              (0 p : IsVar name idx vars) ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
       ||| RHS: no need for further inspection
       ||| The Int is a clause id that allows us to see which of the
       ||| initial clauses are reached in the tree
       STerm : Int -> Term vars -> CaseTree vars
       ||| error from a partial match
       Unmatched : (msg : String) -> CaseTree vars
       ||| Absurd context
       Impossible : CaseTree vars

  ||| Case alternatives. Unlike arbitrary patterns, they can be at most
  ||| one constructor deep.
  public export
  data CaseAlt : List Name -> Type where
       ||| Constructor for a data type; bind the arguments and subterms.
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
       ||| Lazy match for the Delay type use for codata types
       DelayCase : (ty : Name) -> (arg : Name) ->
                   CaseTree (ty :: arg :: vars) -> CaseAlt vars
       ||| Match against a literal
       ConstCase : Constant -> CaseTree vars -> CaseAlt vars
       ||| Catch-all case
       DefaultCase : CaseTree vars -> CaseAlt vars

mutual
  public export
  measure : CaseTree vars -> Nat
  measure (Case idx p scTy xs) = sum $ measureAlts <$> xs
  measure (STerm x y) = 0
  measure (Unmatched msg) = 0
  measure Impossible = 0

  measureAlts : CaseAlt vars -> Nat
  measureAlts (ConCase x tag args y) = 1 + (measure y)
  measureAlts (DelayCase ty arg x) = 1 + (measure x)
  measureAlts (ConstCase x y) = 1 + (measure y)
  measureAlts (DefaultCase x) = 1 + (measure x)

export
isDefault : CaseAlt vars -> Bool
isDefault (DefaultCase _) = True
isDefault _ = False

mutual
  export
  StripNamespace (CaseTree vars) where
    trimNS ns (Case idx p scTy xs)
        = Case idx p (trimNS ns scTy) (map (trimNS ns) xs)
    trimNS ns (STerm x t) = STerm x (trimNS ns t)
    trimNS ns c = c

    restoreNS ns (Case idx p scTy xs)
        = Case idx p (restoreNS ns scTy) (map (restoreNS ns) xs)
    restoreNS ns (STerm x t) = STerm x (restoreNS ns t)
    restoreNS ns c = c

  export
  StripNamespace (CaseAlt vars) where
    trimNS ns (ConCase x tag args t) = ConCase x tag args (trimNS ns t)
    trimNS ns (DelayCase ty arg t) = DelayCase ty arg (trimNS ns t)
    trimNS ns (ConstCase x t) = ConstCase x (trimNS ns t)
    trimNS ns (DefaultCase t) = DefaultCase (trimNS ns t)

    restoreNS ns (ConCase x tag args t) = ConCase x tag args (restoreNS ns t)
    restoreNS ns (DelayCase ty arg t) = DelayCase ty arg (restoreNS ns t)
    restoreNS ns (ConstCase x t) = ConstCase x (restoreNS ns t)
    restoreNS ns (DefaultCase t) = DefaultCase (restoreNS ns t)


public export
data Pat : Type where
     PAs : FC -> Name -> Pat -> Pat
     PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
            List Pat -> Pat
     PTyCon : FC -> Name -> (arity : Nat) -> List Pat -> Pat
     PConst : FC -> (c : Constant) -> Pat
     PArrow : FC -> (x : Name) -> Pat -> Pat -> Pat
     PDelay : FC -> LazyReason -> Pat -> Pat -> Pat
     -- TODO: Matching on lazy types
     PLoc : FC -> Name -> Pat
     PUnmatchable : FC -> Term [] -> Pat

export
isPConst : Pat -> Maybe Constant
isPConst (PConst _ c) = Just c
isPConst _ = Nothing

showCT : {vars : _} -> (indent : String) -> CaseTree vars -> String
showCA : {vars : _} -> (indent : String) -> CaseAlt vars  -> String

showCT indent (Case {name} idx prf ty alts)
  = "case " ++ show name ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of"
  ++ "\n" ++ indent ++ " { "
  ++ showSep ("\n" ++ indent ++ " | ")
             (assert_total (map (showCA ("  " ++ indent)) alts))
  ++ "\n" ++ indent ++ " }"
showCT indent (STerm i tm) = "[" ++ show i ++ "] " ++ show tm
showCT indent (Unmatched msg) = "Error: " ++ show msg
showCT indent Impossible = "Impossible"

showCA indent (ConCase n tag args sc)
        = showSep " " (map show (n :: args)) ++ " => " ++
          showCT indent sc
showCA indent (DelayCase _ arg sc)
        = "Delay " ++ show arg ++ " => " ++ showCT indent sc
showCA indent (ConstCase c sc)
        = "Constant " ++ show c ++ " => " ++ showCT indent sc
showCA indent (DefaultCase sc)
        = "_ => " ++ showCT indent sc

export
covering
{vars : _} -> Show (CaseTree vars) where
  show = showCT ""

export
covering
{vars : _} -> Show (CaseAlt vars) where
  show = showCA ""

mutual
  export
  {vars : _} -> Pretty (CaseTree vars) where
    pretty (Case {name} idx prf ty alts)
      = "case" <++> pretty name <++> ":" <++> pretty ty <++> "of"
         <+> nest 2 (hardline
         <+> vsep (assert_total (map pretty alts)))
    pretty (STerm i tm) = pretty tm
    pretty (Unmatched msg) = pretty "Error:" <++> pretty msg
    pretty Impossible = pretty "Impossible"

  export
  {vars : _} -> Pretty (CaseAlt vars) where
    pretty (ConCase n tag args sc)
      = hsep (map pretty (n :: args)) <++> pretty "=>"
        <+> Union (spaces 1 <+> pretty sc) (nest 2 (hardline <+> pretty sc))
    pretty (DelayCase _ arg sc) =
        pretty "Delay" <++> pretty arg <++> pretty "=>"
        <+> Union (spaces 1 <+> pretty sc) (nest 2 (hardline <+> pretty sc))
    pretty (ConstCase c sc) =
        pretty c <++> pretty "=>"
        <+> Union (spaces 1 <+> pretty sc) (nest 2 (hardline <+> pretty sc))
    pretty (DefaultCase sc) =
        pretty "_ =>"
        <+> Union (spaces 1 <+> pretty sc) (nest 2 (hardline <+> pretty sc))

mutual
  export
  eqTree : CaseTree vs -> CaseTree vs' -> Bool
  eqTree (Case i _ _ alts) (Case i' _ _ alts')
      = i == i'
       && length alts == length alts'
       && all (uncurry eqAlt) (zip alts alts')
  eqTree (STerm _ t) (STerm _ t') = eqTerm t t'
  eqTree (Unmatched _) (Unmatched _) = True
  eqTree Impossible Impossible = True
  eqTree _ _ = False

  eqAlt : CaseAlt vs -> CaseAlt vs' -> Bool
  eqAlt (ConCase n t args tree) (ConCase n' t' args' tree')
      = n == n' && eqTree tree tree' -- assume arities match, since name does
  eqAlt (DelayCase _ _ tree) (DelayCase _ _ tree')
      = eqTree tree tree'
  eqAlt (ConstCase c tree) (ConstCase c' tree')
      = c == c' && eqTree tree tree'
  eqAlt (DefaultCase tree) (DefaultCase tree')
      = eqTree tree tree'
  eqAlt _ _ = False

export
covering
Show Pat where
  show (PAs _ n p) = show n ++ "@(" ++ show p ++ ")"
  show (PCon _ n i _ args) = show n ++ " " ++ show i ++ " " ++ assert_total (show args)
  show (PTyCon _ n _ args) = "<TyCon>" ++ show n ++ " " ++ assert_total (show args)
  show (PConst _ c) = show c
  show (PArrow _ x s t) = "(" ++ show s ++ " -> " ++ show t ++ ")"
  show (PDelay _ _ _ p) = "(Delay " ++ show p ++ ")"
  show (PLoc _ n) = show n
  show (PUnmatchable _ tm) = ".(" ++ show tm ++ ")"

export
Pretty Pat where
  prettyPrec d (PAs _ n p) = pretty n <++> pretty "@" <+> parens (pretty p)
  prettyPrec d (PCon _ n _ _ args) =
    parenthesise (d > Open) $ hsep (pretty n :: map (prettyPrec App) args)
  prettyPrec d (PTyCon _ n _ args) =
    parenthesise (d > Open) $ hsep (pretty n :: map (prettyPrec App) args)
  prettyPrec d (PConst _ c) = pretty c
  prettyPrec d (PArrow _ _ p q) =
    parenthesise (d > Open) $ pretty p <++> pretty "->" <++> pretty q
  prettyPrec d (PDelay _ _ _ p) = parens (pretty "Delay" <++> pretty p)
  prettyPrec d (PLoc _ n) = pretty n
  prettyPrec d (PUnmatchable _ tm) = pretty "." <+> parens (pretty tm)

mutual
  insertCaseNames : SizeOf outer ->
                    SizeOf ns ->
                    CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames outer ns (Case idx prf scTy alts)
      = let MkNVar prf' = insertNVarNames outer ns (MkNVar prf) in
            Case _ prf' (insertNames outer ns scTy)
                (map (insertCaseAltNames outer ns) alts)
  insertCaseNames outer ns (STerm i x) = STerm i (insertNames outer ns x)
  insertCaseNames _ _ (Unmatched msg) = Unmatched msg
  insertCaseNames _ _ Impossible = Impossible

  insertCaseAltNames : SizeOf outer ->
                       SizeOf ns ->
                       CaseAlt (outer ++ inner) ->
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames p q (ConCase x tag args ct)
      = ConCase x tag args
           (rewrite appendAssociative args outer (ns ++ inner) in
                    insertCaseNames (mkSizeOf args + p) q {inner}
                        (rewrite sym (appendAssociative args outer inner) in
                                 ct))
  insertCaseAltNames outer ns (DelayCase tyn valn ct)
      = DelayCase tyn valn
                  (insertCaseNames (suc (suc outer)) ns ct)
  insertCaseAltNames outer ns (ConstCase x ct)
      = ConstCase x (insertCaseNames outer ns ct)
  insertCaseAltNames outer ns (DefaultCase ct)
      = DefaultCase (insertCaseNames outer ns ct)

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames zero ns t

total
getNames : (forall vs . NameMap Bool -> Term vs -> NameMap Bool) ->
           NameMap Bool -> CaseTree vars -> NameMap Bool
getNames add ns sc = getSet ns sc
  where
    mutual
      getAltSet : NameMap Bool -> CaseAlt vs -> NameMap Bool
      getAltSet ns (ConCase n t args sc) = getSet ns sc
      getAltSet ns (DelayCase t a sc) = getSet ns sc
      getAltSet ns (ConstCase i sc) = getSet ns sc
      getAltSet ns (DefaultCase sc) = getSet ns sc

      getAltSets : NameMap Bool -> List (CaseAlt vs) -> NameMap Bool
      getAltSets ns [] = ns
      getAltSets ns (a :: as) = getAltSets (getAltSet ns a) as

      getSet : NameMap Bool -> CaseTree vs -> NameMap Bool
      getSet ns (Case _ x ty xs) = getAltSets ns xs
      getSet ns (STerm i tm) = add ns tm
      getSet ns (Unmatched msg) = ns
      getSet ns Impossible = ns

export
getRefs : (aTotal : Name) -> CaseTree vars -> NameMap Bool
getRefs at = getNames (addRefs False at) empty

export
addRefs : (aTotal : Name) -> NameMap Bool -> CaseTree vars -> NameMap Bool
addRefs at ns = getNames (addRefs False at) ns

export
getMetas : CaseTree vars -> NameMap Bool
getMetas = getNames (addMetas False) empty

export
mkTerm : (vars : List Name) -> Pat -> Term vars
mkTerm vars (PAs fc x y) = mkTerm vars y
mkTerm vars (PCon fc x tag arity xs)
    = apply fc (Ref fc (DataCon tag arity) x)
               (map (mkTerm vars) xs)
mkTerm vars (PTyCon fc x arity xs)
    = apply fc (Ref fc (TyCon 0 arity) x)
               (map (mkTerm vars) xs)
mkTerm vars (PConst fc c) = PrimVal fc c
mkTerm vars (PArrow fc x s t)
    = Bind fc x (Pi fc top Explicit (mkTerm vars s)) (mkTerm (x :: vars) t)
mkTerm vars (PDelay fc r ty p)
    = TDelay fc r (mkTerm vars ty) (mkTerm vars p)
mkTerm vars (PLoc fc n)
    = case isVar n vars of
           Just (MkVar prf) => Local fc Nothing _ prf
           _ => Ref fc Bound n
mkTerm vars (PUnmatchable fc tm) = embed tm
