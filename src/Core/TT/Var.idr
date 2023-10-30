module Core.TT.Var

import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

%default total

public export
data IsVar : a -> Nat -> SnocList a -> Type where
     First : IsVar n Z (ns :< n)
     Later : IsVar n i ns -> IsVar n (S i) (ns :< m)

%name IsVar idx

export
dropLater : IsVar nm (S idx) (vs :< v) -> IsVar nm idx vs
dropLater (Later p) = p

export
mkVar : (wkns : SnocList a) -> IsVar nm (length wkns) (vars :< nm ++ wkns)
mkVar [<] = First
mkVar (ws :< w) = Later (mkVar ws)

public export
dropVar :
  (ns : SnocList a) ->
  {idx : Nat} -> (0 p : IsVar name idx ns) ->
  SnocList a
dropVar (xs :< n) First = xs
dropVar (xs :< n) (Later p) = dropVar xs p :< n

public export
data Var : SnocList a -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

namespace Var

  export
  later : Var ns -> Var (ns :< n)
  later (MkVar p) = MkVar (Later p)

export
sameVar : Var xs -> Var xs -> Bool
sameVar (MkVar {i=x} _) (MkVar {i=y} _) = x == y

export
varIdx : Var xs -> Nat
varIdx (MkVar {i} _) = i

export
dropFirst : List (Var (vs :< n)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

export
Show (Var ns) where
  show (MkVar {i} _) = show i


public export
data NVar : a -> SnocList a -> Type where
     MkNVar : {i : Nat} -> (0 p : IsVar n i vars) -> NVar n vars

namespace NVar
  export
  later : NVar nm ns -> NVar nm (ns :< n)
  later (MkNVar p) = MkNVar (Later p)

export
weakenNVar : SizeOf ns -> NVar name inner -> NVar name (inner ++ ns)
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
             NVar nm (inner ++ outer) ->
             NVar nm (inner :< n ++ outer)
insertNVar p v = case sizedView p of
  Z     => later v
  (S p) => case v of
    MkNVar First     => MkNVar First
    MkNVar (Later v) => later (insertNVar p (MkNVar v))

export
insertVar : SizeOf outer ->
            Var (inner ++ outer) ->
            Var (inner :< n ++ outer)
insertVar p (MkVar v) = let MkNVar v' = insertNVar p (MkNVar v) in MkVar v'


||| The (partial) inverse to insertVar
export
removeVar : SizeOf outer ->
            Var        (inner :< x ++ outer) ->
            Maybe (Var (inner      ++ outer))
removeVar out var = case sizedView out of
  Z => case var of
          MkVar First     => Nothing
          MkVar (Later p) => Just (MkVar p)
  S out' => case var of
              MkVar First     => Just (MkVar First)
              MkVar (Later p) => later <$> removeVar out' (MkVar p)

export
weakenVar : SizeOf ns -> Var inner -> Var (inner ++ ns)
weakenVar p (MkVar v) = let MkNVar v' = weakenNVar p (MkNVar v) in MkVar v'

export
insertNVarNames : SizeOf outer -> SizeOf ns ->
                  NVar name (inner         ++ outer) ->
                  NVar name ((inner ++ ns) ++ outer)
insertNVarNames p q v = case sizedView p of
  Z     => weakenNVar q v
  (S p) => case v of
    MkNVar First      => MkNVar First
    MkNVar (Later v') => later (insertNVarNames p q (MkNVar v'))

export
insertVarNames : SizeOf outer -> SizeOf ns ->
                 Var (inner         ++ outer) ->
                 Var ((inner ++ ns) ++ outer)
insertVarNames p q (MkVar v) = let MkNVar v' = insertNVarNames p q (MkNVar v) in MkVar v'
