module Core.TT

import public Core.FC
import public Core.Name
import public Core.Name.Scoped

import Idris.Pretty.Annotations

import Data.List
import Data.SnocList
import Data.Nat
import Data.String
import Data.Vect
import Decidable.Equality

import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Text.Bounded
import Libraries.Data.String.Extra

import Libraries.Data.SnocList.SizeOf

import public Algebra

import public Core.TT.Binder
import public Core.TT.Primitive
import public Core.TT.Subst
import public Core.TT.Term
import public Core.TT.Term.Subst
import public Core.TT.Var

%default covering

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

namespace CList
  -- A list correspoding to another list
  public export
  data CList : List a -> Type -> Type where
       Nil : CList [] ty
       (::) : (x : ty) -> CList cs ty -> CList (c :: cs) ty


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
data Fixity = InfixL | InfixR | Infix | Prefix

export
Show Fixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix  = "infix"
  show Prefix = "prefix"

export
Interpolation Fixity where
  interpolate = show

export
Eq Fixity where
  InfixL == InfixL = True
  InfixR == InfixR = True
  Infix == Infix = True
  Prefix == Prefix = True
  _ == _ = False


public export
data BindingModifier = NotBinding | Autobind | Typebind

export
Eq BindingModifier where
  NotBinding == NotBinding = True
  Autobind == Autobind = True
  Typebind == Typebind = True
  _ == _ = False

export
Show BindingModifier where
  show NotBinding = "regular"
  show Typebind = "typebind"
  show Autobind = "autobind"

export
Interpolation BindingModifier where
  interpolate = show

-- A record to hold all the information about a fixity
public export
record FixityInfo where
  constructor MkFixityInfo
  fc : FC
  vis : Visibility
  bindingInfo : BindingModifier
  fix : Fixity
  precedence : Nat

export
Show FixityInfo where
  show fx = "fc: \{show fx.fc}, visibility: \{show fx.vis}, binding: \{show fx.bindingInfo}, fixity: \{show fx.fix}, precedence: \{show fx.precedence}"


export
Eq FixityInfo where
  x == y = x.fc == y.fc
        && x.vis == y.vis
        && x.bindingInfo == y.bindingInfo
        && x.fix == y.fix
        && x.precedence == y.precedence

||| Whenever we read an operator from the parser, we don't know if it's a backticked expression with no fixity
||| declaration, or if it has a fixity declaration. If it does not have a declaration, we represent this state
||| with `UndeclaredFixity`.
||| Note that a backticked expression can have a fixity declaration, in which case it is represented with
||| `DeclaredFixity`.
public export
data FixityDeclarationInfo = UndeclaredFixity | DeclaredFixity FixityInfo

-- Left-hand-side information for operators, carries autobind information
-- an operator can either be
-- - not autobind, a regular operator
-- - binding types, such that `(nm : ty) =@ fn nm` desugars into `(=@) ty (\(nm : ty) => fn nm)`
-- - binding expressing with an inferred type such that
--   `(nm := exp) =@ fn nm` desugars into `(=@) exp (\(nm : ?) => fn nm)`
-- - binding both types and expression such that
--   `(nm : ty := exp) =@ fn nm` desugars into `(=@) exp (\(nm : ty) => fn nm)`
public export
data OperatorLHSInfo : tm -> Type where
  -- Traditional operator wihtout binding, carries the lhs
  NoBinder : (lhs : tm) -> OperatorLHSInfo tm
  -- (nm : ty) =@ fn x
  BindType : (name : tm) -> (ty : tm) -> OperatorLHSInfo tm
  -- (nm := exp) =@ fn nm
  BindExpr : (name : tm) -> (expr : tm) -> OperatorLHSInfo tm
  -- (nm : ty := exp) =@ fn nm
  BindExplicitType : (name : tm) ->  (type, expr : tm) -> OperatorLHSInfo tm

export
Show (OperatorLHSInfo tm) where
  show (NoBinder lhs)                    = "regular"
  show (BindType name ty)                = "type-binding (typebind)"
  show (BindExpr name expr)              = "automatically-binding (autobind)"
  show (BindExplicitType name type expr) = "automatically-binding (autobind)"

%name OperatorLHSInfo opInfo

export
Functor OperatorLHSInfo where
  map f (NoBinder lhs) = NoBinder $ f lhs
  map f (BindType nm lhs) = BindType (f nm) (f lhs)
  map f (BindExpr nm lhs) = BindExpr (f nm) (f lhs)
  map f (BindExplicitType nm ty lhs) = BindExplicitType (f nm) (f ty) (f lhs)

export
(.getLhs) : OperatorLHSInfo tm -> tm
(.getLhs) (NoBinder lhs) = lhs
(.getLhs) (BindExpr _ lhs) = lhs
(.getLhs) (BindType _ lhs) = lhs
(.getLhs) (BindExplicitType _ _ lhs) = lhs

export
(.getBoundPat) : OperatorLHSInfo tm -> Maybe tm
(.getBoundPat) (NoBinder lhs) = Nothing
(.getBoundPat) (BindType name ty) = Just name
(.getBoundPat) (BindExpr name expr) = Just name
(.getBoundPat) (BindExplicitType name type expr) = Just name

export
(.getBinder) : OperatorLHSInfo tm -> BindingModifier
(.getBinder) (NoBinder lhs) = NotBinding
(.getBinder) (BindType name ty) = Typebind
(.getBinder) (BindExpr name expr) = Autobind
(.getBinder) (BindExplicitType name type expr) = Autobind

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
       | MissingCases (List (Term [<]))
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

namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

  export
  sizeOf : Bounds xs -> Libraries.Data.List.SizeOf.SizeOf xs
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export
addVars : SizeOf outer -> Bounds bound ->
          NVar name (outer +%+ vars) ->
          NVar name (outer +%+ (bound +%+ vars))
addVars p = insertNVarNames p . sizeOf

export
resolveRef : SizeOf outer ->
             SizeOf done ->
             Bounds bound -> FC -> Name ->
             Maybe (Var (outer +%+ (done <>> (bound +%+ vars))))
resolveRef _ _ None _ _ = Nothing
resolveRef {outer} {vars} {done} p q (Add {xs} new old bs) fc n
    = if n == old
         then Just (weakenNs p (mkVarChiply q))
         else resolveRef p (q :< new) bs fc n

mkLocals : SizeOf outer -> Bounds bound ->
           Term (outer +%+ vars) -> Term (outer +%+ (bound +%+ vars))
mkLocals outer bs (Local fc r idx p)
    = let MkNVar p' = addVars outer bs (MkNVar p) in Local fc r _ p'
mkLocals outer bs (Ref fc Bound name)
    = fromMaybe (Ref fc Bound name) $ do
        MkVar p <- resolveRef outer [<] bs fc name
        pure (Local fc Nothing _ p)
mkLocals outer bs (Ref fc nt name)
    = Ref fc nt name
mkLocals outer bs (Meta fc name y xs)
    = fromMaybe (Meta fc name y (map (mkLocals outer bs) xs)) $ do
        MkVar p <- resolveRef outer [<] bs fc name
        pure (Local fc Nothing _ p)
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
refsToLocals : Bounds bound -> Term vars -> Term (bound +%+ vars)
refsToLocals None y = y
refsToLocals bs y = mkLocals zero  bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :%: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

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
