module Core.TT

import public Core.FC
import public Core.Name

import Data.Bool.Extra
import Data.List
import Data.NameMap
import Data.Vect
import Decidable.Equality
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util

import public Algebra

%default covering

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

public export
data Constant
    = I Int
    | BI Integer
    | B8 Int -- For now, since we don't have Bits types. We need to
                -- make sure the Integer remains in range
    | B16 Int
    | B32 Int
    | B64 Integer
    | Str String
    | Ch Char
    | Db Double
    | WorldVal

    | IntType
    | IntegerType
    | Bits8Type
    | Bits16Type
    | Bits32Type
    | Bits64Type
    | StringType
    | CharType
    | DoubleType
    | WorldType

export
constantEq : (x, y : Constant) -> Maybe (x = y)
constantEq (I x) (I y) = case decEq x y of
                              Yes Refl => Just Refl
                              No contra => Nothing
constantEq (BI x) (BI y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Str x) (Str y) = case decEq x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (Ch x) (Ch y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Db x) (Db y) = Nothing -- no DecEq for Doubles!
constantEq WorldVal WorldVal = Just Refl
constantEq IntType IntType = Just Refl
constantEq IntegerType IntegerType = Just Refl
constantEq StringType StringType = Just Refl
constantEq CharType CharType = Just Refl
constantEq DoubleType DoubleType = Just Refl
constantEq WorldType WorldType = Just Refl
constantEq _ _ = Nothing

export
Show Constant where
  show (I x) = show x
  show (BI x) = show x
  show (B8 x) = show x
  show (B16 x) = show x
  show (B32 x) = show x
  show (B64 x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show WorldVal = "%MkWorld"
  show IntType = "Int"
  show IntegerType = "Integer"
  show Bits8Type = "Bits8"
  show Bits16Type = "Bits16"
  show Bits32Type = "Bits32"
  show Bits64Type = "Bits64"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

export
Pretty Constant where
  pretty (I x) = pretty x
  pretty (BI x) = pretty x
  pretty (B8 x) = pretty x
  pretty (B16 x) = pretty x
  pretty (B32 x) = pretty x
  pretty (B64 x) = pretty x
  pretty (Str x) = dquotes (pretty x)
  pretty (Ch x) = squotes (pretty x)
  pretty (Db x) = pretty x
  pretty WorldVal = pretty "%MkWorld"
  pretty IntType = pretty "Int"
  pretty IntegerType = pretty "Integer"
  pretty Bits8Type = pretty "Bits8"
  pretty Bits16Type = pretty "Bits16"
  pretty Bits32Type = pretty "Bits32"
  pretty Bits64Type = pretty "Bits64"
  pretty StringType = pretty "String"
  pretty CharType = pretty "Char"
  pretty DoubleType = pretty "Double"
  pretty WorldType = pretty "%World"

export
Eq Constant where
  (I x) == (I y) = x == y
  (BI x) == (BI y) = x == y
  (B8 x) == (B8 y) = x == y
  (B16 x) == (B16 y) = x == y
  (B32 x) == (B32 y) = x == y
  (B64 x) == (B64 y) = x == y
  (Str x) == (Str y) = x == y
  (Ch x) == (Ch y) = x == y
  (Db x) == (Db y) = x == y
  WorldVal == WorldVal = True
  IntType == IntType = True
  IntegerType == IntegerType = True
  Bits8Type == Bits8Type = True
  Bits16Type == Bits16Type = True
  Bits32Type == Bits32Type = True
  Bits64Type == Bits64Type = True
  StringType == StringType = True
  CharType == CharType = True
  DoubleType == DoubleType = True
  WorldType == WorldType = True
  _ == _ = False

-- for typecase
export
constTag : Constant -> Int
-- 1 = ->, 2 = Type
constTag IntType = 3
constTag IntegerType = 4
constTag Bits8Type = 5
constTag Bits16Type = 6
constTag Bits32Type = 7
constTag Bits64Type = 8
constTag StringType = 9
constTag CharType = 10
constTag DoubleType = 11
constTag WorldType = 12
constTag _ = 0

-- All the internal operators, parameterised by their arity
public export
data PrimFn : Nat -> Type where
     Add : (ty : Constant) -> PrimFn 2
     Sub : (ty : Constant) -> PrimFn 2
     Mul : (ty : Constant) -> PrimFn 2
     Div : (ty : Constant) -> PrimFn 2
     Mod : (ty : Constant) -> PrimFn 2
     Neg : (ty : Constant) -> PrimFn 1
     ShiftL : (ty : Constant) -> PrimFn 2
     ShiftR : (ty : Constant) -> PrimFn 2

     BAnd : (ty : Constant) -> PrimFn 2
     BOr : (ty : Constant) -> PrimFn 2
     BXOr : (ty : Constant) -> PrimFn 2

     LT  : (ty : Constant) -> PrimFn 2
     LTE : (ty : Constant) -> PrimFn 2
     EQ  : (ty : Constant) -> PrimFn 2
     GTE : (ty : Constant) -> PrimFn 2
     GT  : (ty : Constant) -> PrimFn 2

     StrLength : PrimFn 1
     StrHead : PrimFn 1
     StrTail : PrimFn 1
     StrIndex : PrimFn 2
     StrCons : PrimFn 2
     StrAppend : PrimFn 2
     StrReverse : PrimFn 1
     StrSubstr : PrimFn 3

     DoubleExp : PrimFn 1
     DoubleLog : PrimFn 1
     DoubleSin : PrimFn 1
     DoubleCos : PrimFn 1
     DoubleTan : PrimFn 1
     DoubleASin : PrimFn 1
     DoubleACos : PrimFn 1
     DoubleATan : PrimFn 1
     DoubleSqrt : PrimFn 1
     DoubleFloor : PrimFn 1
     DoubleCeiling : PrimFn 1

     Cast : Constant -> Constant -> PrimFn 1
     BelieveMe : PrimFn 3
     Crash : PrimFn 2

export
Show (PrimFn arity) where
  show (Add ty) = "+" ++ show ty
  show (Sub ty) = "-" ++ show ty
  show (Mul ty) = "*" ++ show ty
  show (Div ty) = "/" ++ show ty
  show (Mod ty) = "%" ++ show ty
  show (Neg ty) = "neg " ++ show ty
  show (ShiftL ty) = "shl " ++ show ty
  show (ShiftR ty) = "shr " ++ show ty
  show (BAnd ty) = "and " ++ show ty
  show (BOr ty) = "or " ++ show ty
  show (BXOr ty) = "xor " ++ show ty
  show (LT ty) = "<" ++ show ty
  show (LTE ty) = "<=" ++ show ty
  show (EQ ty) = "==" ++ show ty
  show (GTE ty) = ">=" ++ show ty
  show (GT ty) = ">" ++ show ty
  show StrLength = "op_strlen"
  show StrHead = "op_strhead"
  show StrTail = "op_strtail"
  show StrIndex = "op_strindex"
  show StrCons = "op_strcons"
  show StrAppend = "++"
  show StrReverse = "op_strrev"
  show StrSubstr = "op_strsubstr"
  show DoubleExp = "op_doubleExp"
  show DoubleLog = "op_doubleLog"
  show DoubleSin = "op_doubleSin"
  show DoubleCos = "op_doubleCos"
  show DoubleTan = "op_doubleTan"
  show DoubleASin = "op_doubleASin"
  show DoubleACos = "op_doubleACos"
  show DoubleATan = "op_doubleATan"
  show DoubleSqrt = "op_doubleSqrt"
  show DoubleFloor = "op_doubleFloor"
  show DoubleCeiling = "op_doubleCeiling"
  show (Cast x y) = "cast-" ++ show x ++ "-" ++ show y
  show BelieveMe = "believe_me"
  show Crash = "crash"

public export
data PiInfo t = Implicit | Explicit | AutoImplicit | DefImplicit t

export
eqPiInfoBy : (t -> u -> Bool) -> PiInfo t -> PiInfo u -> Bool
eqPiInfoBy eqT = go where

  go : PiInfo t -> PiInfo u -> Bool
  go Implicit Implicit = True
  go Explicit Explicit = True
  go AutoImplicit AutoImplicit = True
  go (DefImplicit t) (DefImplicit t') = eqT t t'
  go _ _ = False

-- There's few places where we need the default - it's just when checking if
-- there's a default during elaboration - so often it's easier just to erase it
-- to a normal implicit
export
forgetDef : PiInfo t -> PiInfo t'
forgetDef Explicit = Explicit
forgetDef Implicit = Implicit
forgetDef AutoImplicit = AutoImplicit
forgetDef (DefImplicit t) = Implicit

export
Show t => Show (PiInfo t) where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show AutoImplicit = "AutoImplicit"
  show (DefImplicit t) = "DefImplicit " ++ show t

export
Eq t => Eq (PiInfo t) where
  (==) = eqPiInfoBy (==)

public export
data Binder : Type -> Type where
     -- Lambda bound variables with their implicitness
     Lam : FC -> RigCount -> PiInfo type -> (ty : type) -> Binder type
     -- Let bound variables with their value
     Let : FC -> RigCount -> (val : type) -> (ty : type) -> Binder type
     -- Forall/pi bound variables with their implicitness
     Pi : FC -> RigCount -> PiInfo type -> (ty : type) -> Binder type
     -- pattern bound variables. The PiInfo gives the implicitness at the
     -- point it was bound (Explicit if it was explicitly named in the
     -- program)
     PVar : FC -> RigCount -> PiInfo type -> (ty : type) -> Binder type
     -- variable bound for an as pattern (Like a let, but no computational
     -- force, and only used on the lhs. Converted to a let on the rhs because
     -- we want the computational behaviour.)
     PLet : FC -> RigCount -> (val : type) -> (ty : type) -> Binder type
     -- the type of pattern bound variables
     PVTy : FC -> RigCount -> (ty : type) -> Binder type

export
isLet : Binder t -> Bool
isLet (Let _ _ _ _) = True
isLet _ = False

export
isImplicit : Binder t -> Bool
isImplicit (Pi _ _ Explicit _) = False
isImplicit (Pi _ _ _ _) = True
isImplicit (Lam _ _ Explicit _) = False
isImplicit (Lam _ _ _ _) = True
isImplicit _ = False

export
binderLoc : Binder tm -> FC
binderLoc (Lam fc _ x ty) = fc
binderLoc (Let fc _ val ty) = fc
binderLoc (Pi fc _ x ty) = fc
binderLoc (PVar fc _ p ty) = fc
binderLoc (PLet fc _ val ty) = fc
binderLoc (PVTy fc _ ty) = fc

export
binderType : Binder tm -> tm
binderType (Lam _ _ x ty) = ty
binderType (Let _ _ val ty) = ty
binderType (Pi _ _ x ty) = ty
binderType (PVar _ _ _ ty) = ty
binderType (PLet _ _ val ty) = ty
binderType (PVTy _ _ ty) = ty

export
multiplicity : Binder tm -> RigCount
multiplicity (Lam _ c x ty) = c
multiplicity (Let _ c val ty) = c
multiplicity (Pi _ c x ty) = c
multiplicity (PVar _ c p ty) = c
multiplicity (PLet _ c val ty) = c
multiplicity (PVTy _ c ty) = c

export
piInfo : Binder tm -> PiInfo tm
piInfo (Lam _ c x ty) = x
piInfo (Let _ c val ty) = Explicit
piInfo (Pi _ c x ty) = x
piInfo (PVar _ c p ty) = p
piInfo (PLet _ c val ty) = Explicit
piInfo (PVTy _ c ty) = Explicit

export
setMultiplicity : Binder tm -> RigCount -> Binder tm
setMultiplicity (Lam fc _ x ty) c = Lam fc c x ty
setMultiplicity (Let fc _ val ty) c = Let fc c val ty
setMultiplicity (Pi fc _ x ty) c = Pi fc c x ty
setMultiplicity (PVar fc _ p ty) c = PVar fc c p ty
setMultiplicity (PLet fc _ val ty) c = PLet fc c val ty
setMultiplicity (PVTy fc _ ty) c = PVTy fc c ty

showCount : RigCount -> String
showCount = elimSemi "0 " "1 " (const "")

Show ty => Show (Binder ty) where
	show (Lam _ c _ t) = "\\" ++ showCount c ++ show t
	show (Pi _ c _ t) = "Pi " ++ showCount c ++ show t
	show (Let _ c v t) = "let " ++ showCount c ++ show v ++ " : " ++ show t
	show (PVar _ c _ t) = "pat " ++ showCount c ++ show t
	show (PLet _ c v t) = "plet " ++ showCount c ++ show v ++ " : " ++ show t
	show (PVTy _ c t) = "pty " ++ showCount c ++ show t

export
setType : Binder tm -> tm -> Binder tm
setType (Lam fc c x _) ty = Lam fc c x ty
setType (Let fc c val _) ty = Let fc c val ty
setType (Pi fc c x _) ty = Pi fc c x ty
setType (PVar fc c p _) ty = PVar fc c p ty
setType (PLet fc c val _) ty = PLet fc c val ty
setType (PVTy fc c _) ty = PVTy fc c ty

export
Functor PiInfo where
  map func Explicit = Explicit
  map func Implicit = Implicit
  map func AutoImplicit = AutoImplicit
  map func (DefImplicit t) = (DefImplicit (func t))

export
Functor Binder where
  map func (Lam fc c x ty) = Lam fc c (map func x) (func ty)
  map func (Let fc c val ty) = Let fc c (func val) (func ty)
  map func (Pi fc c x ty) = Pi fc c (map func x) (func ty)
  map func (PVar fc c p ty) = PVar fc c (map func p) (func ty)
  map func (PLet fc c val ty) = PLet fc c (func val) (func ty)
  map func (PVTy fc c ty) = PVTy fc c (func ty)

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} -> (0 p : IsVar name idx ns) -> List Name
dropVar (n :: xs) First = xs
dropVar (n :: xs) (Later p) = n :: dropVar xs p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

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

-- For as patterns matching linear arguments, select which side is
-- consumed
public export
data UseSide = UseLeft | UseRight

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
     Erased : FC -> (imp : Bool) -> -- True == impossible term, for coverage checker
              Term vars
     TType : FC -> Term vars

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
getLoc (TType fc) = fc

export
Eq LazyReason where
  (==) LInf LInf = True
  (==) LLazy LLazy = True
  (==) LUnknown LUnknown = True
  (==) _ _ = False

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
Eq (Term vars) where
  (==) (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
  (==) (Ref _ _ n) (Ref _ _ n') = n == n'
  (==) (Meta _ _ i args) (Meta _ _ i' args')
      = assert_total (i == i' && args == args')
  (==) (Bind _ _ b sc) (Bind _ _ b' sc')
      = assert_total (b == b' && sc == believe_me sc')
  (==) (App _ f a) (App _ f' a') = f == f' && a == a'
  (==) (As _ _ a p) (As _ _ a' p') = a == a' && p == p'
  (==) (TDelayed _ _ t) (TDelayed _ _ t') = t == t'
  (==) (TDelay _ _ t x) (TDelay _ _ t' x') = t == t' && x == x'
  (==) (TForce _ _ t) (TForce _ _ t') = t == t'
  (==) (PrimVal _ c) (PrimVal _ c') = c == c'
  (==) (Erased _ i) (Erased _ i') = i == i'
  (==) (TType _) (TType _) = True
  (==) _ _ = False

-- Check equality, ignoring variable naming
export
eqTerm : Term vs -> Term vs' -> Bool
eqTerm (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
eqTerm (Ref _ _ n) (Ref _ _ n') = n == n'
eqTerm (Meta _ _ i args) (Meta _ _ i' args')
    = assert_total (i == i' && allTrue (zipWith eqTerm args args'))
eqTerm (Bind _ _ b sc) (Bind _ _ b' sc')
    = assert_total (eqBinderBy eqTerm b b') && eqTerm sc sc'
eqTerm (App _ f a) (App _ f' a') = eqTerm f f' && eqTerm a a'
eqTerm (As _ _ a p) (As _ _ a' p') = eqTerm a a' && eqTerm p p'
eqTerm (TDelayed _ _ t) (TDelayed _ _ t') = eqTerm t t'
eqTerm (TDelay _ _ t x) (TDelay _ _ t' x') = eqTerm t t' && eqTerm x x'
eqTerm (TForce _ _ t) (TForce _ _ t') = eqTerm t t'
eqTerm (PrimVal _ c) (PrimVal _ c') = c == c'
eqTerm (Erased _ i) (Erased _ i') = i == i'
eqTerm (TType _) (TType _) = True
eqTerm _ _ = False

public export
interface Weaken (tm : List Name -> Type) where
  weaken : {n, vars : _} -> tm vars -> tm (n :: vars)
  weakenNs : {vars : _} -> (ns : List Name) -> tm vars -> tm (ns ++ vars)

  weakenNs [] t = t
  weakenNs (n :: ns) t = weaken (weakenNs ns t)

  weaken = weakenNs [_]

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Pretty Visibility where
  pretty Private = pretty "private"
  pretty Export = pretty "export"
  pretty Public = pretty "public" <+> pretty "export"

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

export
Eq TotalReq where
    (==) Total Total = True
    (==) CoveringOnly CoveringOnly = True
    (==) PartialOK PartialOK = True
    (==) _ _ = False

export
Show TotalReq where
    show Total = "total"
    show CoveringOnly = "covering"
    show PartialOK = "partial"

public export
data PartialReason
       = NotStrictlyPositive
       | BadCall (List Name)
       | RecPath (List Name)

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n])
      = "possibly not terminating due to call to " ++ show n
  show (BadCall ns)
      = "possibly not terminating due to calls to " ++ showSep ", " (map show ns)
  show (RecPath ns)
      = "possibly not terminating due to recursive path " ++ showSep " -> " (map show ns)

export
Pretty PartialReason where
  pretty NotStrictlyPositive = reflow "not strictly positive"
  pretty (BadCall [n])
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadCall ns)
    = reflow "possibly not terminating due to calls to" <++> concatWith (surround (comma <+> space)) (pretty <$> ns)
  pretty (RecPath ns)
    = reflow "possibly not terminating due to recursive path" <++> concatWith (surround (pretty " -> ")) (pretty <$> ns)

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
Pretty Terminating where
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
Pretty Covering where
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
Pretty Totality where
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

export
weakenNVar : (ns : List Name) ->
             {idx : Nat} -> (0 p : IsVar name idx inner) ->
             NVar name (ns ++ inner)
weakenNVar [] x = MkNVar x
weakenNVar (y :: xs) x
   = let MkNVar x' = weakenNVar xs x in
         MkNVar (Later x')

export
insertNVar : {outer : List Name} ->
            (idx : Nat) ->
            (0 p : IsVar name idx (outer ++ inner)) ->
            NVar name (outer ++ n :: inner)
insertNVar {outer = []} idx x = MkNVar (Later x)
insertNVar {outer = (name :: xs)} Z First = MkNVar First
insertNVar {n} {outer = (x :: xs)} (S i) (Later y)
    = let MkNVar prf = insertNVar {n} i y in
          MkNVar (Later prf)

export
insertVar : {outer : _} ->
            (idx : Nat) ->
            (0 p : IsVar name idx (outer ++ inner)) ->
            Var (outer ++ n :: inner)
insertVar {outer = []} idx x = MkVar (Later x)
insertVar {outer = (name :: xs)} Z First = MkVar First
insertVar {n} {outer = (x :: xs)} (S i) (Later y)
    = let MkVar prf = insertVar {n} i y in
          MkVar (Later prf)

export
weakenVar : (ns : List Name) -> {idx : Nat} -> (0 p : IsVar name idx inner) ->
            Var (ns ++ inner)
weakenVar [] x = MkVar x
weakenVar (y :: xs) x
   = let MkVar x' = weakenVar xs x in
         MkVar (Later x')

export
insertVarNames : {outer, ns : _} ->
                 (idx : Nat) ->
                 (0 p : IsVar name idx (outer ++ inner)) ->
                 Var (outer ++ (ns ++ inner))
insertVarNames {ns} {outer = []} idx prf = weakenVar ns prf
insertVarNames {outer = (y :: xs)} Z First = MkVar First
insertVarNames {ns} {outer = (y :: xs)} (S i) (Later x)
    = let MkVar prf = insertVarNames {ns} i x in
          MkVar (Later prf)

export
insertNVarNames : {outer, ns : _} ->
                  (idx : Nat) ->
                  (0 p : IsVar name idx (outer ++ inner)) ->
                  NVar name (outer ++ (ns ++ inner))
insertNVarNames {ns} {outer = []} idx prf = weakenNVar ns prf
insertNVarNames {outer = (y :: xs)} Z First = MkNVar First
insertNVarNames {ns} {outer = (y :: xs)} (S i) (Later x)
    = let MkNVar prf = insertNVarNames {ns} i x in
          MkNVar (Later prf)

export
insertNames : {outer, inner : _} ->
              (ns : List Name) -> Term (outer ++ inner) ->
              Term (outer ++ (ns ++ inner))
insertNames ns (Local fc r idx prf)
    = let MkNVar prf' = insertNVarNames {ns} idx prf in
          Local fc r _ prf'
insertNames ns (Ref fc nt name) = Ref fc nt name
insertNames ns (Meta fc name idx args)
    = Meta fc name idx (map (insertNames ns) args)
insertNames {outer} {inner} ns (Bind fc x b scope)
    = Bind fc x (assert_total (map (insertNames ns) b))
           (insertNames {outer = x :: outer} {inner} ns scope)
insertNames ns (App fc fn arg)
    = App fc (insertNames ns fn) (insertNames ns arg)
insertNames ns (As fc s as tm)
    = As fc s (insertNames ns as) (insertNames ns tm)
insertNames ns (TDelayed fc r ty) = TDelayed fc r (insertNames ns ty)
insertNames ns (TDelay fc r ty tm)
    = TDelay fc r (insertNames ns ty) (insertNames ns tm)
insertNames ns (TForce fc r tm) = TForce fc r (insertNames ns tm)
insertNames ns (PrimVal fc c) = PrimVal fc c
insertNames ns (Erased fc i) = Erased fc i
insertNames ns (TType fc) = TType fc

export
Weaken Term where
  weakenNs ns tm = insertNames {outer = []} ns tm

export
Weaken Var where
  weaken (MkVar p) = MkVar (Later p)

export
varExtend : IsVar x idx xs -> IsVar x idx (xs ++ ys)
-- What Could Possibly Go Wrong?
-- This relies on the runtime representation of the term being the same
-- after embedding! It is just an identity function at run time, though, and
-- we don't need its definition at compile time, so let's do it...
varExtend p = believe_me p

export
embed : Term vars -> Term (vars ++ more)
embed tm = believe_me tm

public export
ClosedTerm : Type
ClosedTerm = Term []

export
apply : FC -> Term vars -> List (Term vars) -> Term vars
apply loc fn [] = fn
apply loc fn (a :: args) = apply loc (App loc fn a) args

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

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
areVarsCompatible : (xs : List Name) -> (ys : List Name) ->
                    Maybe (CompatibleVars xs ys)
areVarsCompatible [] [] = pure CompatPre
areVarsCompatible (x :: xs) (y :: ys)
    = do compat <- areVarsCompatible xs ys
         pure (CompatExt compat)
areVarsCompatible _ _ = Nothing

extendCompats : (args : List Name) ->
                CompatibleVars xs ys ->
                CompatibleVars (args ++ xs) (args ++ ys)
extendCompats [] prf = prf
extendCompats (x :: xs) prf = CompatExt (extendCompats xs prf)

renameLocalRef : CompatibleVars xs ys ->
                 {idx : Nat} ->
                 (0 p : IsVar name idx xs) ->
                 Var ys
renameLocalRef prf p = believe_me (MkVar p)
-- renameLocalRef CompatPre First = (MkVar First)
-- renameLocalRef (CompatExt x) First = (MkVar First)
-- renameLocalRef CompatPre (Later p) = (MkVar (Later p))
-- renameLocalRef (CompatExt y) (Later p)
--     = let (MkVar p') = renameLocalRef y p in MkVar (Later p')

renameVarList : CompatibleVars xs ys -> Var xs -> Var ys
renameVarList prf (MkVar p) = renameLocalRef prf p

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars compat tm = believe_me tm -- no names in term, so it's identity
-- This is how we would define it:
-- renameVars CompatPre tm = tm
-- renameVars prf (Local fc r idx vprf)
--     = let MkVar vprf' = renameLocalRef prf vprf in
--           Local fc r _ vprf'
-- renameVars prf (Ref fc x name) = Ref fc x name
-- renameVars prf (Meta fc n i args)
--     = Meta fc n i (map (renameVars prf) args)
-- renameVars prf (Bind fc x b scope)
--     = Bind fc x (map (renameVars prf) b) (renameVars (CompatExt prf) scope)
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
renameTop m tm = renameVars (CompatExt CompatPre) tm

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
  shrinkTerm (Local fc r idx loc) prf
     = case subElem loc prf of
            Nothing => Nothing
            Just (MkVar loc') => Just (Local fc r _ loc')
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
  shrinkTerm (Erased fc i) prf = Just (Erased fc i)
  shrinkTerm (TType fc) prf = Just (TType fc)

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
embedSub sub (Erased fc i) = Erased fc i
embedSub sub (TType fc) = TType fc

namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

export
addVars : {later, bound : _} ->
          {idx : Nat} ->
          Bounds bound -> (0 p : IsVar name idx (later ++ vars)) ->
          NVar name (later ++ (bound ++ vars))
addVars {later = []} {bound} bs p = weakenNVar bound p
addVars {later = (x :: xs)} bs First = MkNVar First
addVars {later = (x :: xs)} bs (Later p)
  = let MkNVar p' = addVars {later = xs} bs p in
        MkNVar (Later p')

resolveRef : {later : _} ->
             (done : List Name) -> Bounds bound -> FC -> Name ->
             Maybe (Term (later ++ (done ++ bound ++ vars)))
resolveRef done None fc n = Nothing
resolveRef {later} {vars} done (Add {xs} new old bs) fc n
    = if n == old
         then rewrite appendAssociative later done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar {inner = new :: xs ++ vars}
                                        (later ++ done) First in
                     Just (Local fc Nothing _ p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef (done ++ [new]) bs fc n

mkLocals : {later, bound : _} ->
           Bounds bound ->
           Term (later ++ vars) -> Term (later ++ (bound ++ vars))
mkLocals bs (Local fc r idx p)
    = let MkNVar p' = addVars bs p in Local fc r _ p'
mkLocals bs (Ref fc Bound name)
    = maybe (Ref fc Bound name) id (resolveRef [] bs fc name)
mkLocals bs (Ref fc nt name)
    = Ref fc nt name
mkLocals bs (Meta fc name y xs)
    = maybe (Meta fc name y (map (mkLocals bs) xs))
            id (resolveRef [] bs fc name)
mkLocals {later} bs (Bind fc x b scope)
    = Bind fc x (map (mkLocals bs) b)
           (mkLocals {later = x :: later} bs scope)
mkLocals bs (App fc fn arg)
    = App fc (mkLocals bs fn) (mkLocals bs arg)
mkLocals bs (As fc s as tm)
    = As fc s (mkLocals bs as) (mkLocals bs tm)
mkLocals bs (TDelayed fc x y)
    = TDelayed fc x (mkLocals bs y)
mkLocals bs (TDelay fc x t y)
    = TDelay fc x (mkLocals bs t) (mkLocals bs y)
mkLocals bs (TForce fc r x)
    = TForce fc r (mkLocals bs x)
mkLocals bs (PrimVal fc c) = PrimVal fc c
mkLocals bs (Erased fc i) = Erased fc i
mkLocals bs (TType fc) = TType fc

export
refsToLocals : {bound : _} ->
               Bounds bound -> Term vars -> Term (bound ++ vars)
refsToLocals None y = y
refsToLocals bs y = mkLocals {later = []} bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Var ns)
isVar n [] = Nothing
isVar n (m :: ms)
    = case nameEq n m of
           Nothing => do MkVar p <- isVar n ms
                         pure (MkVar (Later p))
           Just Refl => pure (MkVar First)

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : List Name) -> Term vars -> Term vars
resolveNames vars (Ref fc Bound name)
    = case isVar name vars of
           Just (MkVar prf) => Local fc (Just False) _ prf
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

  findDrop : {drop : _} -> {idx : Nat} ->
             FC -> Maybe Bool -> (0 p : IsVar name idx (drop ++ vars)) ->
             SubstEnv drop vars -> Term vars
  findDrop {drop = []} fc r var env = Local fc r _ var
  findDrop {drop = x :: xs} fc r First (tm :: env) = tm
  findDrop {drop = x :: xs} fc r (Later p) (tm :: env)
      = findDrop fc r p env

  find : {drop, vars, outer : _} -> {idx : Nat} ->
         FC -> Maybe Bool -> (0 p : IsVar name idx (outer ++ (drop ++ vars))) ->
         SubstEnv drop vars ->
         Term (outer ++ vars)
  find {outer = []} fc r var env = findDrop fc r var env
  find {outer = x :: xs} fc r First env = Local fc r _ First
  find {outer = x :: xs} fc r (Later p) env = weaken (find fc r p env)

  substEnv : {drop, vars, outer : _} ->
             SubstEnv drop vars -> Term (outer ++ (drop ++ vars)) ->
             Term (outer ++ vars)
  substEnv env (Local fc r _ prf)
      = find fc r prf env
  substEnv env (Ref fc x name) = Ref fc x name
  substEnv env (Meta fc n i xs)
      = Meta fc n i (map (substEnv env) xs)
  substEnv {outer} env (Bind fc x b scope)
      = Bind fc x (map (substEnv env) b)
                  (substEnv {outer = x :: outer} env scope)
  substEnv env (App fc fn arg)
      = App fc (substEnv env fn) (substEnv env arg)
  substEnv env (As fc s as pat)
      = As fc s (substEnv env as) (substEnv env pat)
  substEnv env (TDelayed fc x y) = TDelayed fc x (substEnv env y)
  substEnv env (TDelay fc x t y)
      = TDelay fc x (substEnv env t) (substEnv env y)
  substEnv env (TForce fc r x) = TForce fc r (substEnv env x)
  substEnv env (PrimVal fc c) = PrimVal fc c
  substEnv env (Erased fc i) = Erased fc i
  substEnv env (TType fc) = TType fc

  export
  substs : {drop, vars : _} ->
           SubstEnv drop vars -> Term (drop ++ vars) -> Term vars
  substs env tm = substEnv {outer = []} env tm

  export
  subst : {vars, x : _} -> Term vars -> Term (x :: vars) -> Term vars
  subst val tm = substEnv {outer = []} {drop = [_]} [val] tm

-- Replace an explicit name with a term
export
substName : {vars : _} -> Name -> Term vars -> Term vars -> Term vars
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
addMetas : NameMap Bool -> Term vars -> NameMap Bool
addMetas ns (Local fc x idx y) = ns
addMetas ns (Ref fc x name) = ns
addMetas ns (Meta fc n i xs) = addMetaArgs (insert n False ns) xs
  where
    addMetaArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addMetaArgs ns [] = ns
    addMetaArgs ns (t :: ts) = addMetaArgs (addMetas ns t) ts
addMetas ns (Bind fc x (Let _ c val ty) scope)
    = addMetas (addMetas (addMetas ns val) ty) scope
addMetas ns (Bind fc x b scope)
    = addMetas (addMetas ns (binderType b)) scope
addMetas ns (App fc fn arg)
    = addMetas (addMetas ns fn) arg
addMetas ns (As fc s as tm) = addMetas ns tm
addMetas ns (TDelayed fc x y) = addMetas ns y
addMetas ns (TDelay fc x t y)
    = addMetas (addMetas ns t) y
addMetas ns (TForce fc r x) = addMetas ns x
addMetas ns (PrimVal fc c) = ns
addMetas ns (Erased fc i) = ns
addMetas ns (TType fc) = ns

-- Get the metavariable names in a term
export
getMetas : Term vars -> NameMap Bool
getMetas tm = addMetas empty tm

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
addRefs ua at ns (Erased fc i) = ns
addRefs ua at ns (TType fc) = ns

-- As above, but for references. Also flag whether a name is under an
-- 'assert_total' because we may need to know that in coverage/totality
-- checking
export
getRefs : (aTotal : Name) -> Term vars -> NameMap Bool
getRefs at tm = addRefs False at empty tm

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

export
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local {name} _ c idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ _ n) [] = show n
      showApp (Meta _ n i args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind _ x (Lam _ c p ty) sc) []
          = "\\" ++ showCount c ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind _ x (Let _ c val ty) sc) []
          = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++
            " = " ++ show val ++ " in " ++ show sc
      showApp (Bind _ x (Pi _ c Explicit ty) sc) []
          = "((" ++ showCount c ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind _ x (Pi _ c Implicit ty) sc) []
          = "{" ++ showCount c ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind _ x (Pi _ c AutoImplicit ty) sc) []
          = "{auto " ++ showCount c ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind _ x (Pi _ c (DefImplicit tm) ty) sc) []
          = "{default " ++ show tm ++ " "
                ++ showCount c ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind _ x (PVar _ c Explicit ty) sc) []
          = "pat " ++ showCount c ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind _ x (PVar _ c Implicit ty) sc) []
          = "{pat " ++ showCount c ++ show x ++ " : " ++ show ty ++
            "} => " ++ show sc
      showApp (Bind _ x (PVar _ c AutoImplicit ty) sc) []
          = "{auto pat " ++ showCount c ++ show x ++ " : " ++ show ty ++
            "} => " ++ show sc
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
      showApp (Erased _ _) [] = "[__]"
      showApp (TType _) [] = "Type"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
