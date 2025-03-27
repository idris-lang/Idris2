module Core.TT.Var

import Data.Fin
import Data.List
import Data.Nat
import Data.So
import Data.SnocList
import Data.Vect

import Core.Name
import Core.Name.Scoped
import Core.Name.CompatibleVars

import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

import Data.List.HasLength
import Libraries.Data.List.HasLength
import Libraries.Data.List.SizeOf

import Libraries.Data.Erased

%default total

------------------------------------------------------------------------
-- IsVar Predicate

||| IsVar n k ns is a proof that
||| the name n
||| is a position k
||| in the snoclist ns
public export
data IsVar : a -> Nat -> Scopeable a -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

%name IsVar idx

export
finIdx : {idx : _} -> (0 prf : IsVar x idx vars) ->
         Fin (length vars)
finIdx First = FZ
finIdx (Later l) = FS (finIdx l)

||| Recover the value pointed at by an IsVar proof
||| O(n) in the size of the index
export
nameAt : {vars : Scopeable a} -> {idx : Nat} -> (0 p : IsVar n idx vars) -> a
nameAt {vars = n :: _} First = n
nameAt (Later p) = nameAt p

||| Inversion principle for Later
export
dropLater : IsVar nm (S idx) (n :: ns) -> IsVar nm idx ns
dropLater (Later p) = p

export
0 mkIsVar : HasLength m inner -> IsVar nm m (inner ++ nm :: outer)
mkIsVar Z = First
mkIsVar (S x) = Later (mkIsVar x)

export
0 mkIsVarChiply : HasLength m inner -> IsVar nm m (inner <>> nm :: outer)
mkIsVarChiply hl
  = rewrite chipsAsListAppend inner (nm :: outer) in
    rewrite sym $ plusZeroRightNeutral m in
    mkIsVar (hlChips hl Z)

||| Compute the remaining scope once the target variable has been removed
public export
dropIsVar :
  (ns : Scopeable a) ->
  {idx : Nat} -> (0 p : IsVar name idx ns) ->
  Scopeable a
dropIsVar (_ :: xs) First = xs
dropIsVar (n :: xs) (Later p) = n :: dropIsVar xs p

||| Throw in extra variables on the outer side of the context
||| This is essentially the identity function
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 embedIsVar : IsVar x idx xs -> IsVar x idx (xs ++ outer)
embedIsVar First = First
embedIsVar (Later p) = Later (embedIsVar p)

||| Throw in extra variables on the local end of the context.
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 weakenIsVar : (s : SizeOf ns) -> IsVar x idx xs -> IsVar x (size s + idx) (ns ++ xs)
weakenIsVar (MkSizeOf Z Z) p =  p
weakenIsVar (MkSizeOf (S k) (S l)) p =  Later (weakenIsVar (MkSizeOf k l) p)

0 locateIsVarLT :
  (s : SizeOf local) ->
  So (idx < size s) ->
  IsVar x idx (local ++ outer) ->
  IsVar x idx local
locateIsVarLT (MkSizeOf Z Z) so v = case v of
  First impossible
  Later v impossible
locateIsVarLT (MkSizeOf (S k) (S l)) so v = case v of
  First => First
  Later v => Later (locateIsVarLT (MkSizeOf k l) so v)

0 locateIsVarGE :
  (s : SizeOf local) ->
  So (idx >= size s) ->
  IsVar x idx (local ++ outer) ->
  IsVar x (idx `minus` size s) outer
locateIsVarGE (MkSizeOf Z Z) so v = rewrite minusZeroRight idx in v
locateIsVarGE (MkSizeOf (S k) (S l)) so v = case v of
  Later v => locateIsVarGE (MkSizeOf k l) so v

export
locateIsVar : {idx : Nat} -> (s : SizeOf local) ->
  (0 p : IsVar x idx (local ++ outer)) ->
  Either (Erased (IsVar x idx local))
         (Erased (IsVar x (idx `minus` size s) outer))
locateIsVar s p = case choose (idx < size s) of
  Left so => Left (MkErased (locateIsVarLT s so p))
  Right so => Right (MkErased (locateIsVarGE s so p))

------------------------------------------------------------------------
-- Variable in scope

||| A variable in a scope is a name, a De Bruijn index,
||| and a proof that the name is at that position in the scope.
||| Everything but the De Bruijn index is erased.
public export
record Var {0 a : Type} (vars : Scopeable a) where
  constructor MkVar
  {varIdx : Nat}
  {0 varNm : a}
  0 varPrf : IsVar varNm varIdx vars

namespace Var

  export
  later : Var ns -> Var (n :: ns)
  later (MkVar p) = MkVar (Later p)

  export
  isLater : Var (n :: vs) -> Maybe (Var vs)
  isLater (MkVar First) = Nothing
  isLater (MkVar (Later p)) = Just (MkVar p)

export
mkVar : SizeOf inner -> Var (inner ++ nm :: outer)
mkVar (MkSizeOf s p) = MkVar (mkIsVar p)

export
mkVarChiply : SizeOf inner -> Var (inner <>> nm :: outer)
mkVarChiply (MkSizeOf s p) = MkVar (mkIsVarChiply p)

||| Generate all variables
export
allVars : (vars : Scope) -> List (Var vars)
allVars = go [<] where

  go : SizeOf local -> (vs : Scope) -> List (Var (local <>> vs))
  go s [] = []
  go s (v :: vs) = mkVarChiply s :: go (s :< v) vs

export
Eq (Var xs) where
  v == w = varIdx v == varIdx w


||| Removing var 0, strengthening all the other ones
export
dropFirst : Scopeable (Var (n :: vs)) -> Scopeable (Var vs)
dropFirst = List.mapMaybe isLater

||| Manufacturing a thinning from a list of variables to keep
export
thinFromVars :
  (vars : _) -> Scopeable (Var vars) ->
  (newvars ** Thin newvars vars)
thinFromVars [] els
    = (_ ** Refl)
thinFromVars (x :: xs) els
    = let (vs ** subRest) = thinFromVars xs (dropFirst els) in
      if MkVar First `elem` els
        then (x :: vs ** Keep subRest)
        else (vs ** Drop subRest)

export
Show (Var ns) where
  show v = show (varIdx v)

------------------------------------------------------------------------
-- Named variable in scope

public export
record NVar {0 a : Type} (nm : a) (vars : Scopeable a) where
  constructor MkNVar
  {nvarIdx : Nat}
  0 nvarPrf : IsVar nm nvarIdx vars

namespace NVar
  export
  later : NVar nm ns -> NVar nm (n :: ns)
  later (MkNVar p) = MkNVar (Later p)

  export
  isLater : NVar nm (n :: ns) -> Maybe (NVar nm ns)
  isLater (MkNVar First) = Nothing
  isLater (MkNVar (Later p)) = Just (MkNVar p)

export
forgetName : NVar nm vars -> Var vars
forgetName (MkNVar p) = MkVar p

export
recoverName : (v : Var vars) -> NVar (varNm v) vars
recoverName (MkVar p) = MkNVar p

export
mkNVar : SizeOf inner -> NVar nm (inner ++ nm :: outer)
mkNVar (MkSizeOf s p) = MkNVar (mkIsVar p)

export
mkNVarChiply : SizeOf inner -> NVar nm (inner <>> nm :: outer)
mkNVarChiply (MkSizeOf s p) = MkNVar (mkIsVarChiply p)

export
locateNVar : SizeOf local -> NVar nm (local ++ outer) ->
             Either (NVar nm local) (NVar nm outer)
locateNVar s (MkNVar p) = case locateIsVar s p of
  Left p => Left (MkNVar (runErased p))
  Right p => Right (MkNVar (runErased p))

public export
dropNVar : {ns : Scopeable a} -> NVar nm ns -> Scopeable a
dropNVar (MkNVar p) = dropIsVar ns p

------------------------------------------------------------------------
-- Scope checking

export
isDeBruijn : Nat -> (vars : Scope) -> Maybe (Var vars)
isDeBruijn Z (_ :: _) = pure (MkVar First)
isDeBruijn (S k) (_ :: vs) = later <$> isDeBruijn k vs
isDeBruijn _ _ = Nothing

export
isNVar : (n : Name) -> (ns : Scope) -> Maybe (NVar n ns)
isNVar n [] = Nothing
isNVar n (m :: ms)
    = case nameEq n m of
           Nothing   => map later (isNVar n ms)
           Just Refl => pure (MkNVar First)

export
isVar : (n : Name) -> (ns : Scope) -> Maybe (Var ns)
isVar n ns = forgetName <$> isNVar n ns

export
locateVar : SizeOf local -> Var (local ++ outer) ->
            Either (Var local) (Var outer)
locateVar s v  = bimap forgetName forgetName
  $ locateNVar s (recoverName v)

------------------------------------------------------------------------
-- Weakening

export
weakenNVar : SizeOf ns -> NVar name outer -> NVar name (ns ++ outer)
weakenNVar s (MkNVar {nvarIdx} p)
  = MkNVar {nvarIdx = plus (size s) nvarIdx} (weakenIsVar s p)

export
embedNVar : NVar name ns -> NVar name (ns ++ outer)
embedNVar (MkNVar p) = MkNVar (embedIsVar p)

export
insertNVar : SizeOf local ->
             NVar nm (local ++ outer) ->
             NVar nm (local ++ n :: outer)
insertNVar p v = case locateNVar p v of
  Left v => embedNVar v
  Right v => weakenNVar p (later v)

export
insertNVarChiply : SizeOf local ->
  NVar nm (local <>> outer) ->
  NVar nm (local <>> n :: outer)
insertNVarChiply p v
  = rewrite chipsAsListAppend local (n :: outer) in
    insertNVar (p <>> zero)
  $ replace {p = NVar nm} (chipsAsListAppend local outer) v

export
insertNVarNames : GenWeakenable (NVar name)
insertNVarNames p q v = case locateNVar p v of
  Left v => embedNVar v
  Right v =>
    rewrite appendAssociative local ns outer in
    weakenNVar (p + q) v

||| The (partial) inverse to insertNVar
export
removeNVar : SizeOf local ->
         NVar nm (local ++ n :: outer) ->
  Maybe (NVar nm (local ++      outer))
removeNVar s var = case locateNVar s var of
  Left v => pure (embedNVar v)
  Right v => weakenNVar s <$> isLater v

export
insertVar : SizeOf local ->
  Var (local ++ outer) ->
  Var (local ++ n :: outer)
insertVar p v = forgetName $ insertNVar p (recoverName v)

weakenVar : SizeOf ns -> Var outer -> Var (ns ++ outer)
weakenVar p v = forgetName $ weakenNVar p (recoverName v)

insertVarNames : GenWeakenable Var
insertVarNames p q v = forgetName $ insertNVarNames p q (recoverName v)

||| The (partial) inverse to insertVar
export
removeVar : SizeOf local ->
         Var (local ++ n :: outer) ->
  Maybe (Var (local ++      outer))
removeVar s var = forgetName <$> removeNVar s (recoverName var)

------------------------------------------------------------------------
-- Strengthening

export
strengthenIsVar : {n : Nat} -> (s : SizeOf inner) ->
  (0 p : IsVar x n (inner ++ vars)) ->
  Maybe (Erased (IsVar x (n `minus` size s) vars))
strengthenIsVar s p = case locateIsVar s p of
  Left _ => Nothing
  Right p => pure p

strengthenVar : SizeOf inner ->
  Var (inner ++ vars) -> Maybe (Var vars)
strengthenVar s (MkVar p)
  = do MkErased p <- strengthenIsVar s p
       pure (MkVar p)

strengthenNVar : SizeOf inner ->
  NVar x (inner ++ vars) -> Maybe (NVar x vars)
strengthenNVar s (MkNVar p)
  = do MkErased p <- strengthenIsVar s p
       pure (MkNVar p)

------------------------------------------------------------------------
-- Reindexing

0 lookup :
  CompatibleVars xs ys ->
  {idx : Nat} ->
  (0 p : IsVar {a} name idx xs) ->
  a
lookup Pre p = name
lookup (Ext {m} x) First = m
lookup (Ext x) (Later p) = lookup x p

0 compatIsVar :
  (ns : CompatibleVars xs ys) ->
  {idx : Nat} -> (0 p : IsVar name idx xs) ->
  IsVar (lookup ns p) idx ys
compatIsVar Pre p = p
compatIsVar (Ext {n} x) First = First
compatIsVar (Ext {n} x) (Later p) = Later (compatIsVar x p)

compatVar : CompatibleVars xs ys -> Var xs -> Var ys
compatVar prf (MkVar p) = MkVar (compatIsVar prf p)

------------------------------------------------------------------------
-- Thinning

export
thinIsVar : {idx : Nat} -> (0 p : IsVar name idx xs) ->
  Thin xs ys -> Var ys
thinIsVar p Refl = MkVar p
thinIsVar p (Drop th) = later (thinIsVar p th)
thinIsVar First (Keep th) = MkVar First
thinIsVar (Later p) (Keep th) = later (thinIsVar p th)

export
shrinkIsVar : {idx : Nat} -> (0 p : IsVar name idx xs) ->
  Thin ys xs -> Maybe (Var ys)
shrinkIsVar prf Refl = Just (MkVar prf)
shrinkIsVar First (Drop p) = Nothing
shrinkIsVar (Later x) (Drop p) = shrinkIsVar x p
shrinkIsVar First (Keep p) = Just (MkVar First)
shrinkIsVar (Later x) (Keep p) = later <$> shrinkIsVar x p

------------------------------------------------------------------------
-- Putting it all together

export
%hint
0 FreelyEmbeddableIsVar : FreelyEmbeddable (IsVar x k)
FreelyEmbeddableIsVar = MkFreelyEmbeddable embedIsVar

export
GenWeaken (Var {a = Name}) where
  genWeakenNs = insertVarNames

%hint
export
WeakenVar : Weaken (Var {a = Name})
WeakenVar = GenWeakenWeakens

export
Strengthen (Var {a = Name}) where
  strengthenNs = strengthenVar

export
FreelyEmbeddable (Var {a = Name}) where
  embed (MkVar p) = MkVar (embedIsVar p)

export
IsScoped (Var {a = Name}) where
  compatNs = compatVar

  thin (MkVar p) = thinIsVar p
  shrink (MkVar p) = shrinkIsVar p

export
GenWeaken (NVar {a = Name} nm) where
  genWeakenNs = insertNVarNames

%hint
export
WeakenNVar : Weaken (NVar {a = Name} nm)
WeakenNVar = GenWeakenWeakens

export
Strengthen (NVar {a = Name} nm) where
  strengthenNs = strengthenNVar

export
FreelyEmbeddable (NVar {a = Name} nm) where
  embed (MkNVar p) = MkNVar (embedIsVar p)

------------------------------------------------------------------------
-- Corollaries

||| Moving the zeroth variable under a set number of variables
export
shiftUnderNs : SizeOf {a = Name} inner ->
               {idx : _} ->
               (0 p : IsVar n idx (x :: inner ++ outer)) ->
               NVar n (inner ++ x :: outer)
shiftUnderNs s First = weakenNs s (MkNVar First)
shiftUnderNs s (Later p) = insertNVar s (MkNVar p)
