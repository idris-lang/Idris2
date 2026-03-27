module Core.Evaluate.Value

import Core.Context
import Core.Core
import Core.TT
import Core.Options

import Data.SnocList
import Data.Vect
import Data.List1
import Data.String

import Libraries.Data.WithDefault

public export
data Form = Glue | Normal

public export
data Value : Form -> SnocList Name -> Type

public export
Glued : SnocList Name -> Type
Glued = Value Glue

public export
NF : SnocList Name -> Type
NF = Value Normal

public export
ClosedNF : Type
ClosedNF = NF [<]

public export
data VCaseAlt : SnocList Name -> Type

public export
record SpineEntry vars where
  constructor MkSpineEntry
  loc : FC
  multiplicity : RigCount
  value : Core (Glued vars)

public export
0 Spine : SnocList Name -> Type
Spine vars = SnocList (SpineEntry vars)

-- The 'Form' is a phantom type index that says whether we know the value is
-- in normal form, or whether it might be 'Glued'
-- In theory, we know that everything except 'VApp' and "VMeta' are Normal,
-- but in practice this is annoying because evaluating doesn't know whether
-- it's going to produce a 'Glued' or a 'Normal'.
-- The phantom index gives us enough help, specifically in that it means we
-- are sure that we've expanded to head normal Normal form before processing
-- a Value
public export
data Value : Form -> SnocList Name -> Type where
     VBind : FC -> (x : Name) -> Binder (Glued vars) ->
             (sc : Core (Glued vars) -> Core (Glued vars)) ->
             Value f vars
     -- A 'glued' application. This includes the original application
     -- (for quoting back HNFs) and what it reduces to (if the name is
     -- defined).
     VApp : FC ->
            NameType -> Name -> Spine vars -> -- original form
            Core (Maybe (Glued vars)) -> -- the normal form
            Value f vars
     VLocal   : FC -> (idx : Nat) -> (0 p : IsVar n idx vars) ->
                Spine vars ->
                Value f vars
     VMeta  : FC -> Name -> Int -> -- Name and resolved name of metavar
              List (RigCount, Core (Glued vars)) -> -- Scope of metavar
              Spine vars ->
              Core (Maybe (Glued vars)) -> -- the normal form, if solved
              Value f vars
     VDCon    : FC -> Name -> (tag : Tag) -> (arity : Nat) ->
                Spine vars -> Value f vars
     VTCon    : FC -> Name -> (arity : Nat) ->
                Spine vars -> Value f vars
     VAs      : FC -> UseSide -> Value f vars -> Value f vars -> Value f vars
     VCase    : FC -> CaseType ->
                RigCount -> (sc : NF vars) -> (scTy : Glued vars) ->
                List (VCaseAlt vars) ->
                Value f vars
     VDelayed : FC -> LazyReason -> Glued vars -> Value f vars
     VDelay   : FC -> LazyReason -> Glued vars -> Glued vars -> Value f vars
     VForce   : FC -> LazyReason -> Glued vars -> Spine vars -> Value f vars
     VPrimVal : FC -> Constant -> Value f vars
     VPrimOp  : {ar : _} ->
                FC -> PrimFn ar -> Vect ar (Glued vars) -> Value f vars
     VErased  : FC -> WhyErased (Value f vars) -> Value f vars
     VUnmatched : FC -> String -> Value f vars
     VType    : FC -> Name -> Value f vars

export
vRef : FC -> NameType -> Name -> Value f vars
vRef fc nt n = VApp fc nt n [<] (pure Nothing)

export
vtCon : FC -> Name -> Nat -> Spine vars -> Value f vars
vtCon fc (UN (Basic "Type")) Z [<] = VType fc (MN "top" 0)
vtCon fc n Z [<] = case isConstantType n of
  Just c => VPrimVal fc $ PrT c
  Nothing => VTCon fc n Z [<]
vtCon fc n arity args = VTCon fc n arity args

-- It's safe to pretend an NF is Glued, if we need it
export
asGlued : Value f vars -> Glued vars
asGlued = believe_me -- justification as above

export
getLoc : Value f vars -> FC
getLoc (VBind fc x y sc) = fc
getLoc (VApp fc x y sx z) = fc
getLoc (VLocal fc idx p sx) = fc
getLoc (VMeta fc x y xs sx z) = fc
getLoc (VDCon fc x tag arity sx) = fc
getLoc (VTCon fc x arity sx) = fc
getLoc (VAs fc x y z) = fc
getLoc (VCase fc t x sc scTy xs) = fc
getLoc (VDelayed fc x y) = fc
getLoc (VDelay fc x y z) = fc
getLoc (VForce fc x y sx) = fc
getLoc (VPrimVal fc x) = fc
getLoc (VPrimOp fc x xs) = fc
getLoc (VErased fc imp) = fc
getLoc (VUnmatched fc x) = fc
getLoc (VType fc x) = fc

export
HasNames (Value f vars)

export
covering
{free : _} -> Show (Value f free)

public export
0 VCaseScope : SnocList (RigCount, Name) -> SnocList Name -> Type
VCaseScope [<] vars = Core (List (Glued vars, Glued vars), Glued vars)
VCaseScope (xs :< x) vars = Core (Glued vars) -> VCaseScope xs vars

public export
data VCaseAlt : SnocList Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     VConCase : FC -> Name -> (tag : Int) ->
                (args : SnocList (RigCount, Name)) ->
                VCaseScope args vars -> VCaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     VDelayCase : FC -> (ty : Name) -> (arg : Name) ->
                  VCaseScope [<(Algebra.Preorder.top, arg), (Algebra.Semiring.erased, ty)] vars ->
                  VCaseAlt vars
     ||| Match against a literal
     VConstCase : FC -> Constant -> Glued vars -> VCaseAlt vars
     ||| Catch-all case
     VDefaultCase : FC -> Glued vars -> VCaseAlt vars

export
covering
{vars : _} -> Show (VCaseAlt vars) where
  show (VConCase _ ty _ args scoped) = "VConCase \{show ty} \{show args}"
  show (VDelayCase _ ty arg scoped) = "VDelayCase \{show ty} \{show arg}"
  show (VConstCase _ c vars_glued) = "VConstCase \{show c} \{show vars_glued}"
  show (VDefaultCase _ vars_glued) = "VDefaultCase \{show vars_glued}"

export
HasNames (VCaseAlt free) where
  full defs (VConCase fc n tag args cl) = pure $ VConCase fc !(full defs n) tag args cl
  full defs (VDelayCase fc n arg cl) = pure $ VDelayCase fc !(full defs n) arg cl
  full defs (VConstCase fc c cl) = pure $ VConstCase fc c cl
  full defs (VDefaultCase fc cl) = pure $ VDefaultCase fc cl

  resolved defs (VConCase fc n tag args cl) = pure $ VConCase fc !(resolved defs n) tag args cl
  resolved defs (VDelayCase fc n arg cl) = pure $ VDelayCase fc !(resolved defs n) arg cl
  resolved defs (VConstCase fc c cl) = pure $ VConstCase fc c cl
  resolved defs (VDefaultCase fc cl) = pure $ VDefaultCase fc cl

export
HasNames (Value f vars) where
  full defs (VBind fc x bd f) = pure $ VBind fc x bd f
  full defs (VApp fc x y xs z) = pure $ VApp fc x !(full defs y) xs z
  full defs (VDCon fc n tag arity xs) = pure $ VDCon fc !(full defs n) tag arity xs
  full defs (VTCon fc n arity xs) = pure $ VTCon fc !(full defs n) arity xs
  full defs (VAs fc side nf nf1) = pure $ VAs fc side !(full defs nf) !(full defs nf1)
  full defs (VCase fc ct rc sc scTy alts) = pure $ VCase fc ct rc !(full defs sc) scTy !(traverse (full defs) alts)
  full defs (VDelayed fc lz nf) = pure $ VDelayed fc lz !(full defs nf)
  full defs (VDelay fc lz cl cl1) = pure $ VDelay fc lz cl cl1
  full defs (VForce fc lz nf xs) = pure $ VForce fc lz !(full defs nf) xs
  full defs (VPrimVal fc cst) = pure $ VPrimVal fc cst
  full defs (VPrimOp fc op args) = pure $ VPrimOp fc op !(traverseVect (full defs) args)
  full defs (VErased fc imp) = pure $ VErased fc imp
  full defs (VUnmatched fc n) = pure $ VUnmatched fc n
  full defs (VType fc n) = pure $ VType fc !(full defs n)
  full defs (VLocal fc n v sp) = pure $ VLocal fc n v sp
  full defs (VMeta fc n i vs sp f) = pure $ VMeta fc !(full defs n) i vs sp f

  resolved defs (VBind fc x bd f) = pure $ VBind fc x bd f
  resolved defs (VApp fc x y xs z) = pure $ VApp fc x !(resolved defs y) xs z
  resolved defs (VDCon fc n tag arity xs) = pure $ VDCon fc !(resolved defs n) tag arity xs
  resolved defs (VTCon fc n arity xs) = pure $ VTCon fc !(resolved defs n) arity xs
  resolved defs (VAs fc side nf nf1) = pure $ VAs fc side !(resolved defs nf) !(resolved defs nf1)
  resolved defs (VCase fc ct rc sc scTy alts) = pure $ VCase fc ct rc !(resolved defs sc) scTy !(resolved defs alts)
  resolved defs (VDelayed fc lz nf) = pure $ VDelayed fc lz !(resolved defs nf)
  resolved defs (VDelay fc lz cl cl1) = pure $ VDelay fc lz cl cl1
  resolved defs (VForce fc lz nf xs) = pure $ VForce fc lz !(resolved defs nf) xs
  resolved defs (VPrimVal fc cst) = pure $ VPrimVal fc cst
  resolved defs (VPrimOp fc op args) = pure $ VPrimOp fc op !(traverseVect (resolved defs) args)
  resolved defs (VErased fc imp) = pure $ VErased fc imp
  resolved defs (VUnmatched fc n) = pure $ VUnmatched fc n
  resolved defs (VType fc n) = pure $ VType fc !(resolved defs n)
  resolved defs (VLocal fc n v sp) = pure $ VLocal fc n v sp
  resolved defs (VMeta fc n i vs sp f) = pure $ VMeta fc !(resolved defs n) i vs sp f

export
covering
{free : _} -> Show (Value f free) where
  show (VBind _ x (Lam _ c info ty) _)
    = "\\" ++ withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
      " => [closure]"
  show (VBind _ x (Let _ c val ty) _)
    = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (VBind _ x (Pi _ c info ty) _)
    = withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
      " -> [closure]"
  show (VBind _ x (PVar _ c info ty) _)
    = withPiInfo info ("pat " ++ showCount c ++ show x ++ " : " ++ show ty) ++
      " => [closure]"
  show (VBind _ x (PLet _ c val ty) _)
    = "plet " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (VBind _ x (PVTy _ c ty) _)
    = "pty " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " => [closure]"
  show (VApp _ _ n sp _) = show n ++ " [" ++ show (length sp) ++ " closures]"
  show (VLocal{}) = "Local"
  show (VMeta _ n _ _ _ _) = "Meta " ++ show n
  show (VDCon _ n _ _ sp) = show n ++ " %DCon [" ++ show (length sp) ++ " closures]"
  show (VTCon _ n _ sp) = show n ++ " %TCon [" ++ show (length sp) ++ " closures]"
  show (VCase _ ct rc vars_nf vars_glued alts) = "Case { \{show ct} \{show vars_nf} \{show vars_glued} \{show alts} }"
  show (VPrimVal _ c) = "Constant " ++ show c
  show (VPrimOp _ f args) = "PrimOp " ++ show f ++ " " ++ show (length args)
  show (VAs _ _ n tm) = show n ++ "@" ++ show tm
  show (VDelayed _ _ tm) = "%Delayed " ++ show tm
  show (VDelay _ _ _ _) = "%Delay [closure]"
  show (VForce _ _ tm args) = "%Force " ++ show tm ++ " [" ++ show (length args) ++ " closures]"
  show (VErased _ w) = "[_\{show w}_]"
  show (VUnmatched _ str) = "Unmatched: " ++ show str
  show (VType _ n) = "Type \{show n}"
