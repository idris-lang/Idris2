module Core.TT.Var

import Core.Name.Scoped
import Core.Name.CompatibleVars

import Data.DPair
import Data.Fin
import Data.List
import Data.List.HasLength
import Data.So
import Data.SnocList

import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.List.SizeOf
import Libraries.Data.Erased

%default total

------------------------------------------------------------------------
-- IsVar Predicate

-- TODO need a copy of `IsVar` for both

||| IsVar n k ns is a proof that
||| the name n
||| is a position k
||| in the snoclist ns
public export
data IsVar : a -> Nat -> SnocList a -> Type where
     First : IsVar n Z (ns :< n)
     Later : IsVar n i ns -> IsVar n (S i) (ns :< m)

%name IsVar idx

namespace List
  ||| IsVar n k ns is a proof that
  ||| the name n
  ||| is a position k
  ||| in the list ns
  public export
  data IsVarL : a -> Nat -> List a -> Type where
      First : IsVarL n Z (n :: ns)
      Later : IsVarL n i ns -> IsVarL n (S i) (m :: ns)

  %name IsVarL idx

-- `vs` is available in the erased fragment, and the case builder
-- pattern-matches on it. To simplify the case tree and help the
-- coverage checker, we use an explicit dot pattern here.
-- TODO: remove `{vs = .(_)}` once the compiler generates more optimal case trees.
export
0 Last : HasLength (S n) vs -> Exists (\ nm => IsVar nm n vs)
Last {vs = .(_)} (S Z) = Evidence _ First
Last {vs = .(_)} (S (S p)) = bimap id Later (Last (S p))

export
finIdx : {idx : _} -> (0 prf : IsVar x idx vars) ->
         Fin (length vars)
finIdx First = FZ
finIdx (Later l) = FS (finIdx l)

||| Recover the value pointed at by an IsVar proof
||| O(n) in the size of the index
-- TODO make return type a Singleton
export
nameAt : {vars : SnocList a} -> {idx : Nat} -> (0 p : IsVar n idx vars) -> a
nameAt {vars = _ :< n} First = n
nameAt (Later p) = nameAt p

||| Inversion principle for Later
export
dropLater : IsVar nm (S idx) (ns :< n) -> IsVar nm idx ns
dropLater (Later p) = p

export
0 appendIsVar : HasLength m inner -> IsVar nm m (outer :< nm ++ inner)
appendIsVar Z = First
appendIsVar (S x) = Later (appendIsVar x)

export
0 isVarFishily : HasLength m inner -> IsVar nm m (outer :< nm <>< inner)
isVarFishily hl
  = rewrite fishAsSnocAppend (outer :< nm) inner in
    appendIsVar
  $ rewrite sym $ plusZeroRightNeutral m in
    hlFish Z hl

export
0 mkIsVar : HasLength m inner -> IsVar nm m (outer :< nm ++ inner)
mkIsVar Z = First
mkIsVar (S x) = Later (mkIsVar x)

||| Compute the remaining scope once the target variable has been removed
public export
dropIsVar :
  (ns : SnocList a) ->
  {idx : Nat} -> (0 p : IsVar name idx ns) ->
  SnocList a
dropIsVar (xs :< _) First = xs
dropIsVar (xs :< n) (Later p) = dropIsVar xs p :< n

||| Compute the remaining scope once the target variable has been removed
public export
dropIsVarL : (ns : List a) -> {idx : Nat} -> (0 _ : IsVarL nm idx ns) -> List a
dropIsVarL (_ :: xs) First = xs
dropIsVarL (n :: xs) (Later p) = n :: dropIsVarL xs p

||| Throw in extra variables on the outer side of the context
||| This is essentially the identity function
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 embedIsVar : IsVar x idx vars -> IsVar x idx (more ++ vars)
embedIsVar First = First
embedIsVar (Later p) = Later (embedIsVar p)

||| Throw in extra variables on the local end of the context.
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 weakenIsVar : (s : SizeOf ns) -> IsVar x idx xs -> IsVar x (size s + idx) (xs ++ ns)
weakenIsVar (MkSizeOf Z Z) p =  p
weakenIsVar (MkSizeOf (S k) (S l)) p =  Later (weakenIsVar (MkSizeOf k l) p)

||| Throw in extra variables on the local end of the context.
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 weakenIsVarL : (s : SizeOf ns) -> IsVarL x idx xs -> IsVarL x (size s + idx) (ns ++ xs)
weakenIsVarL (MkSizeOf Z Z) p =  p
weakenIsVarL (MkSizeOf (S k) (S l)) p =  Later (weakenIsVarL (MkSizeOf k l) p)

0 locateIsVarLT :
  (s : SizeOf inner) ->
  So (idx < size s) ->
  IsVar x idx (outer ++ inner) ->
  IsVar x idx inner
locateIsVarLT (MkSizeOf Z Z) so v = case v of
  First impossible
  Later v impossible
locateIsVarLT (MkSizeOf (S k) (S l)) so v = case v of
  First => First
  Later v => Later (locateIsVarLT (MkSizeOf k l) so v)

0 locateIsVarGE :
  (s : SizeOf inner) ->
  So (idx >= size s) ->
  IsVar x idx (outer ++ inner) ->
  IsVar x (idx `minus` size s) outer
locateIsVarGE (MkSizeOf Z Z) so v = rewrite minusZeroRight idx in v
locateIsVarGE (MkSizeOf (S k) (S l)) so v = case v of
  Later v => locateIsVarGE (MkSizeOf k l) so v

export
locateIsVar : {idx : Nat} -> (s : SizeOf inner) ->
  (0 p : IsVar x idx (outer ++ inner)) ->
  Either (Erased (IsVar x (idx `minus` size s) outer))
         (Erased (IsVar x idx inner))
locateIsVar s p = case choose (idx < size s) of
  Left so => Right (MkErased (locateIsVarLT s so p))
  Right so => Left (MkErased (locateIsVarGE s so p))

------------------------------------------------------------------------
-- Variable in scope

||| A variable in a scope is a name, a De Bruijn index,
||| and a proof that the name is at that position in the scope.
||| Everything but the De Bruijn index is erased.
public export
record Var {0 a : Type} (vars : SnocList a) where
  constructor MkVar
  {varIdx : Nat}
  {0 varNm : a}
  0 varPrf : IsVar varNm varIdx vars

namespace Var

  export
  first : Var (ns :< n)
  first = MkVar First

  export
  later : Var ns -> Var (ns :< n)
  later (MkVar p) = MkVar (Later p)

  export
  isLater : Var (vs :< n) -> Maybe (Var vs)
  isLater (MkVar First) = Nothing
  isLater (MkVar (Later p)) = Just (MkVar p)

  export
  last : SizeOf vs -> Maybe (Var vs)
  last (MkSizeOf Z p) = Nothing
  last (MkSizeOf (S n) p) = Just (MkVar (snd $ Last p))

export
mkVar : SizeOf inner -> Var (Scope.addInner (Scope.bind outer nm) inner)
mkVar (MkSizeOf s p) = MkVar (mkIsVar p)

export
mkVarFishily : SizeOf inner -> Var (outer :< nm <>< inner)
mkVarFishily (MkSizeOf s p) = MkVar (isVarFishily p)

namespace SnocList
  ||| Generate all variables
  export
  allVars : (vars : Scope) -> Scopeable (Var vars)
  allVars = go zero where
    go : SizeOf inner -> (vs : Scope) -> Scopeable (Var (vs <>< inner))
    go s [<] = [<]
    go s (vs :< v) = go (suc s) vs :< mkVarFishily s

namespace List
  ||| Generate all variables
  export
  allVars : (vars : List Name) -> List (Var ([<] <>< vars))
  allVars vs = toList $ SnocList.allVars (cast vs)

export
Eq (Var xs) where
  v == w = varIdx v == varIdx w

export
Show (Var ns) where
  show v = show (varIdx v)

------------------------------------------------------------------------
-- Named variable in scope

public export
record NVar {0 a : Type} (nm : a) (vars : SnocList a) where
  constructor MkNVar
  {nvarIdx : Nat}
  0 nvarPrf : IsVar nm nvarIdx vars

namespace List
  public export
  record NVarL {0 a : Type} (nm : a) (vars : List a) where
    constructor MkNVarL
    {nvarIdx : Nat}
    0 nvarPrf : IsVarL nm nvarIdx vars

namespace NVar

  export
  first : NVar n (ns :< n)
  first = MkNVar First

  export
  later : NVar nm ns -> NVar nm (ns :< n)
  later (MkNVar p) = MkNVar (Later p)

  export
  isLater : NVar nm (ns :< n) -> Maybe (NVar nm ns)
  isLater (MkNVar First) = Nothing
  isLater (MkNVar (Later p)) = Just (MkNVar p)

export
forgetName : NVar nm vars -> Var vars
forgetName (MkNVar p) = MkVar p

export
recoverName : (v : Var vars) -> NVar (varNm v) vars
recoverName (MkVar p) = MkNVar p

export
mkNVar : SizeOf inner -> NVar nm (outer :< nm ++ inner)
mkNVar (MkSizeOf s p) = MkNVar (mkIsVar p)

export
locateNVar : SizeOf inner -> NVar nm (outer ++ inner) ->
             Either (NVar nm outer) (NVar nm inner)
locateNVar s (MkNVar p) = case locateIsVar s p of
  Left p => Left (MkNVar (runErased p))
  Right p => Right (MkNVar (runErased p))

public export
dropNVar : {ns : SnocList a} -> NVar nm ns -> SnocList a
dropNVar (MkNVar p) = dropIsVar ns p

------------------------------------------------------------------------
-- Scope checking

export
isDeBruijn : Nat -> (vars : SnocList Name) -> Maybe (Var vars)
isDeBruijn Z (_ :< _) = pure first
isDeBruijn (S k) (vs :< _) = later <$> isDeBruijn k vs
isDeBruijn _ _ = Nothing

export
isNVar : (n : Name) -> (ns : SnocList Name) -> Maybe (NVar n ns)
isNVar n [<] = Nothing
isNVar n (ms :< m)
    = case nameEq n m of
           Nothing   => map later (isNVar n ms) -- TODO make tail-recursive
           Just Refl => pure (MkNVar First)

export
isVar : (n : Name) -> (ns : SnocList Name) -> Maybe (Var ns)
isVar n ns = forgetName <$> isNVar n ns

export
locateVar : SizeOf inner -> Var (outer ++ inner) ->
            Either (Var outer) (Var inner)
locateVar s v  = bimap forgetName forgetName
  $ locateNVar s (recoverName v)

------------------------------------------------------------------------
-- Weakening

%inline export
weakenNVar : Weakenable (NVar name)
weakenNVar s (MkNVar p) = MkNVar (weakenIsVar s p)

export
weakenNVarL : SizeOf ns -> NVarL nm inner -> NVarL nm (ns ++ inner)
weakenNVarL s (MkNVarL p) = MkNVarL (weakenIsVarL s p)

export
embedNVar : NVar name inner -> NVar name (outer ++ inner)
embedNVar (MkNVar p) = MkNVar (embedIsVar p)

export
insertNVar : SizeOf inner ->
             NVar nm (outer ++ inner) ->
             NVar nm (outer :< n ++ inner)
insertNVar p v = case locateNVar p v of
  Left v => weakenNVar p (later v)
  Right v => embedNVar v

export
insertNVarFishy : SizeOf inner ->
             NVar nm (outer <>< inner) ->
             NVar nm (outer :< n <>< inner)
insertNVarFishy p v
  = rewrite fishAsSnocAppend (outer :< n) inner in
    insertNVar (zero <>< p)
  $ replace {p = NVar nm} (fishAsSnocAppend outer inner) v

export
insertNVarNames : GenWeakenable (NVar name)
insertNVarNames p q v = case locateNVar q v of
  Left v => weakenNVar q (weakenNVar p v)
  Right v => embedNVar v

export
insertVar : SizeOf inner ->
  Var (outer ++ inner) ->
  Var (outer :< n ++ inner)
insertVar p v = forgetName $ insertNVar p (recoverName v)

weakenVar : Weakenable Var
weakenVar p v = forgetName $ weakenNVar p (recoverName v)

insertVarNames : GenWeakenable Var
insertVarNames p q v = forgetName $ insertNVarNames p q (recoverName v)

------------------------------------------------------------------------
-- Strengthening

export
strengthenIsVar : {n : Nat} -> (s : SizeOf inner) ->
  (0 p : IsVar x n (outer ++ inner)) ->
  Maybe (Erased (IsVar x (n `minus` size s) outer))
strengthenIsVar s p = case locateIsVar s p of
  Left p => pure p
  Right _ => Nothing

strengthenVar : Strengthenable Var
strengthenVar s (MkVar p)
  = do MkErased p <- strengthenIsVar s p
       pure (MkVar p)

strengthenNVar : Strengthenable (NVar name)
strengthenNVar s (MkNVar p)
  = do MkErased p <- strengthenIsVar s p
       pure (MkNVar p)

------------------------------------------------------------------------
-- Reindexing

namespace CompatibleVars
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

  export
  compatVar : CompatibleVars xs ys -> Var xs -> Var ys
  compatVar prf (MkVar p) = MkVar (compatIsVar prf p)

------------------------------------------------------------------------
-- Thinning

export
thinIsVar : {idx : Nat} -> (0 p : IsVar name idx xs) ->
  Thin xs ys -> Var ys
thinIsVar p Refl = MkVar p
thinIsVar p (Drop th) = later (thinIsVar p th)
thinIsVar First (Keep th) = first
thinIsVar (Later p) (Keep th) = later (thinIsVar p th)

export
shrinkIsVar : {idx : Nat} -> (0 p : IsVar name idx xs) ->
  Thin ys xs -> Maybe (Var ys)
shrinkIsVar prf Refl = Just (MkVar prf)
shrinkIsVar First (Drop p) = Nothing
shrinkIsVar (Later x) (Drop p) = shrinkIsVar x p
shrinkIsVar First (Keep p) = Just first
shrinkIsVar (Later x) (Keep p) = later <$> shrinkIsVar x p

------------------------------------------------------------------------
-- Putting it all together

export
%hint
0 FreelyEmbeddableIsVar : FreelyEmbeddable (IsVar x k)
FreelyEmbeddableIsVar = MkFreelyEmbeddable embedIsVar

export
GenWeaken Var where
  genWeakenNs = insertVarNames

%hint
export
WeakenVar : Weaken Var
WeakenVar = GenWeakenWeakens

export
Strengthen Var where
  strengthenNs = strengthenVar

export
FreelyEmbeddable Var where
  embed (MkVar p) = MkVar (embedIsVar p)

export
IsScoped Var where
  compatNs = CompatibleVars.compatVar

  thin (MkVar p) = thinIsVar p
  shrink (MkVar p) = shrinkIsVar p

export
GenWeaken (NVar nm) where
  genWeakenNs = insertNVarNames

%hint
export
WeakenNVar : Weaken (NVar nm)
WeakenNVar = GenWeakenWeakens

export
Strengthen (NVar nm) where
  strengthenNs = strengthenNVar

export
FreelyEmbeddable (NVar nm) where
  embed (MkNVar p) = MkNVar (embedIsVar p)

------------------------------------------------------------------------
-- Corollaries

||| Moving the zeroth variable under a set number of variables
export
shiftUnderNs : SizeOf {a = Name} args ->
               {idx : _} ->
               (0 p : IsVar n idx (vars ++ args :< x)) ->
               NVar n (vars :< x ++ args)
shiftUnderNs s First = weakenNs s (MkNVar First)
shiftUnderNs s (Later p) = insertNVar s (MkNVar p)

export
shiftUndersN : SizeOf {a = Name} args ->
               {idx : _} ->
               (0 p : IsVar n idx (vars <>< args :< x)) ->
               NVar n (vars :< x <>< args)
shiftUndersN s First = weakensN s (MkNVar First)
shiftUndersN s (Later p) = insertNVarFishy s (MkNVar p)

namespace IsVar
  export
  lookup : {idx : _}  -> All p vs -> (0 _ : IsVar x idx vs) -> p x
  lookup (xs :< x) First = x
  lookup (xs :< x) (Later p) = lookup xs p

namespace Var
  export %inline
  lookup : All p vs -> (v : Var vs) -> p (varNm v)
  lookup vs (MkVar p) = lookup vs p
