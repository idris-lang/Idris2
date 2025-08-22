module Core.TT.Binder

import Algebra

import Core.FC

%default total

------------------------------------------------------------------------
-- Pi information classifies the kind of pi type this is

public export
data PiInfo t =
  ||| Implicit Pi types (e.g. {0 a : Type} -> ...)
  ||| The argument is to be solved by unification
  Implicit |
  ||| Explicit Pi types (e.g. (x : a) -> ...)
  ||| The argument is to be passed explicitly
  Explicit |
  ||| Auto Pi types (e.g. (fun : Functor f) => ...)
  ||| The argument is to be solved by proof search
  AutoImplicit |
  ||| Default Pi types (e.g. {default True flag : Bool} -> ...)
  ||| The argument is set to the default value if nothing is
  ||| passed explicitly
  DefImplicit t

%name PiInfo pinfo

namespace PiInfo

  export
  isImplicit : PiInfo t -> Bool
  isImplicit Explicit = False
  isImplicit _ = True

||| Heterogeneous equality, provided an heterogeneous equality
||| of default values
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
------------------------------------------------------------------------
-- A bound value

||| A bound value along with its `PiInfo`.
||| We cannot use `PiInfo` as metadata for `WithData` because the record is functorial in both
||| `t` and `PiInfo`.
public export
record PiBindData (t : Type) where
  constructor MkPiBindData
  info : PiInfo t
  boundType : t

public export
mapType : (t -> t) -> PiBindData t -> PiBindData t
mapType f = {boundType $= f}

export
Show t => Show (PiBindData t) where
  show bind = show bind.info ++ ", " ++ show bind.boundType
------------------------------------------------------------------------
-- Different types of binders we may encounter

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

%name Binder bd

export
isLet : Binder t -> Bool
isLet (Let {}) = True
isLet _ = False

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
isImplicit : Binder tm -> Bool
isImplicit = PiInfo.isImplicit . piInfo

export
setMultiplicity : Binder tm -> RigCount -> Binder tm
setMultiplicity (Lam fc _ x ty) c = Lam fc c x ty
setMultiplicity (Let fc _ val ty) c = Let fc c val ty
setMultiplicity (Pi fc _ x ty) c = Pi fc c x ty
setMultiplicity (PVar fc _ p ty) c = PVar fc c p ty
setMultiplicity (PLet fc _ val ty) c = PLet fc c val ty
setMultiplicity (PVTy fc _ ty) c = PVTy fc c ty

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
Foldable PiInfo where
  foldr f acc Implicit = acc
  foldr f acc Explicit = acc
  foldr f acc AutoImplicit = acc
  foldr f acc (DefImplicit x) = f x acc

export
Traversable PiInfo where
  traverse f Implicit = pure Implicit
  traverse f Explicit = pure Explicit
  traverse f AutoImplicit = pure AutoImplicit
  traverse f (DefImplicit x) = map DefImplicit (f x)

export
Functor PiBindData where
  map f (MkPiBindData info type) = MkPiBindData (map f info) (f type)

export
Foldable PiBindData where
  foldr f acc (MkPiBindData info type) = f type (foldr f acc info)

export
Traversable PiBindData where
  traverse f (MkPiBindData info type) = MkPiBindData <$> traverse f info <*> f type

export
Functor Binder where
  map func (Lam fc c x ty) = Lam fc c (map func x) (func ty)
  map func (Let fc c val ty) = Let fc c (func val) (func ty)
  map func (Pi fc c x ty) = Pi fc c (map func x) (func ty)
  map func (PVar fc c p ty) = PVar fc c (map func p) (func ty)
  map func (PLet fc c val ty) = PLet fc c (func val) (func ty)
  map func (PVTy fc c ty) = PVTy fc c (func ty)

export
Foldable Binder where
  foldr f acc (Lam fc c x ty) = foldr f (f ty acc) x
  foldr f acc (Let fc c val ty) = f val (f ty acc)
  foldr f acc (Pi fc c x ty) = foldr f (f ty acc) x
  foldr f acc (PVar fc c p ty) = foldr f (f ty acc) p
  foldr f acc (PLet fc c val ty) = f val (f ty acc)
  foldr f acc (PVTy fc c ty) = f ty acc

export
Traversable Binder where
  traverse f (Lam fc c x ty) = Lam fc c <$> traverse f x <*> f ty
  traverse f (Let fc c val ty) = Let fc c <$> f val <*> f ty
  traverse f (Pi fc c x ty) = Pi fc c <$> traverse f x <*> f ty
  traverse f (PVar fc c p ty) = PVar fc c <$> traverse f p <*> f ty
  traverse f (PLet fc c val ty) = PLet fc c <$> f val <*> f ty
  traverse f (PVTy fc c ty) = PVTy fc c <$> f ty


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
