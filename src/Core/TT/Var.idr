module Core.TT.Var

import Data.Fin
import Data.Nat
import Data.So
import Data.SnocList
import Data.Vect

import Core.Name
import Core.Name.Scoped

import Libraries.Data.List.HasLength
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

import Libraries.Data.SnocList.Extra

%default total

------------------------------------------------------------------------
-- IsVar Predicate

||| IsVar n k ns is a proof that
||| the name n
||| is a position k
||| in the snoclist ns
public export
data IsVar : a -> Nat -> SnocList a -> Type where
     First : IsVar n Z (ns :< n)
     Later : IsVar n i ns -> IsVar n (S i) (ns :< m)

%name IsVar idx

export
finIdx : {idx : _} -> (0 prf : IsVar x idx vars) ->
         Fin (length vars)
finIdx First = FZ
finIdx (Later l) = FS (finIdx l)


||| Recover the value pointed at by an IsVar proof
export
nameAt : {vars : SnocList a} -> {idx : Nat} -> (0 p : IsVar n idx vars) -> a
nameAt {vars = _ :< n} First = n
nameAt (Later p) = nameAt p

||| Inversion principle for Later
export
dropLater : IsVar nm (S idx) (vs :< v) -> IsVar nm idx vs
dropLater (Later p) = p

export
appendIsVar : HasLength m inner -> IsVar nm m (outer :< nm ++ inner)
appendIsVar Z = First
appendIsVar (S x) = Later (appendIsVar x)

export
fishyIsVar : HasLength m inner -> IsVar nm m (outer :< nm <>< inner)
fishyIsVar hl
  = rewrite fishAsSnocAppend (outer :< nm) inner in
    appendIsVar
  $ rewrite sym $ plusZeroRightNeutral m in
    hlFish Z hl

export
mkVar : (wkns : SnocList a) -> IsVar nm (length wkns) (outer :< nm ++ wkns)
mkVar [<] = First
mkVar (ws :< w) = Later (mkVar ws)

||| Compute the remaining scope once the target variable has been removed
public export
dropVar :
  (ns : SnocList a) ->
  {idx : Nat} -> (0 p : IsVar name idx ns) ->
  SnocList a
dropVar (xs :< n) First = xs
dropVar (xs :< n) (Later p) = dropVar xs p :< n

||| Throw in extra variables on the outer side of the context
||| This is essentially the identity function
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 embedIsVar : IsVar x idx xs -> IsVar x idx (outer ++ xs)
embedIsVar First = First
embedIsVar (Later p) = Later (embedIsVar p)

||| Throw in extra variables on the local end of the context.
||| This is slow so we ensure it's only used in a runtime irrelevant manner
export
0 weakenIsVar : (s : SizeOf ns) -> IsVar x idx xs -> IsVar x (size s + idx) (xs ++ ns)
weakenIsVar (MkSizeOf Z Z) p =  p
weakenIsVar (MkSizeOf (S k) (S l)) p =  Later (weakenIsVar (MkSizeOf k l) p)

0 locateIsVarLT :
  (s : SizeOf local) ->
  So (idx < size s) ->
  IsVar x idx (outer ++ local) ->
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
  IsVar x idx (outer ++ local) ->
  IsVar x (idx `minus` size s) outer
locateIsVarGE (MkSizeOf Z Z) so v = rewrite minusZeroRight idx in v
locateIsVarGE (MkSizeOf (S k) (S l)) so v = case v of
  Later v => locateIsVarGE (MkSizeOf k l) so v

------------------------------------------------------------------------
-- Variable in scope

||| A variable in a scope is a name, a De Bruijn index,
||| and a proof that the name is at that position in the scope.
||| Everything but the De Bruijn index is erased.
public export
record Var (vars : SnocList a) where
  constructor MkVar
  {varIdx : Nat}
  {0 varNm : a}
  0 varPrf : IsVar varNm varIdx vars

namespace Var

  export
  later : Var ns -> Var (ns :< n)
  later (MkVar p) = MkVar (Later p)

export
appendVar : SizeOf inner -> Var (outer :< nm ++ inner)
appendVar (MkSizeOf s p) = MkVar (appendIsVar p)

export
fishyVar : SizeOf inner -> Var (outer :< nm <>< inner)
fishyVar (MkSizeOf s p) = MkVar (fishyIsVar p)

export
Eq (Var xs) where
  v == w = varIdx v == varIdx w

||| Removing var 0, strengthening all the other ones
export
dropFirst : List (Var (vs :< n)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

||| Manufacturing a thinning from a list of variables to keep
export
thinFromVars :
  (vars : _) -> List (Var vars) ->
  (newvars ** Thin newvars vars)
thinFromVars [<] els
    = (_ ** Refl)
thinFromVars (xs :< x) els
    = let (_ ** subRest) = thinFromVars xs (dropFirst els) in
      if MkVar First `elem` els
        then (_ ** keep subRest)
        else (_ ** Drop subRest)

export
Show (Var ns) where
  show v = show (varIdx v)

------------------------------------------------------------------------
-- Named variable in scope

public export
record NVar (nm : a) (vars : SnocList a) where
  constructor MkNVar
  {nvarIdx : Nat}
  0 nvarPrf : IsVar nm nvarIdx vars

namespace NVar
  export
  later : NVar nm ns -> NVar nm (ns :< n)
  later (MkNVar p) = MkNVar (Later p)

export
forgetName : NVar nm vars -> Var vars
forgetName (MkNVar p) = MkVar p

export
appendNVar : SizeOf inner -> NVar nm (outer :< nm ++ inner)
appendNVar (MkSizeOf s p) = MkNVar (appendIsVar p)

export
fishyNVar : SizeOf inner -> NVar nm (outer :< nm <>< inner)
fishyNVar (MkSizeOf s p) = MkNVar (fishyIsVar p)

export
locateNVar : SizeOf local -> NVar nm (outer ++ local) ->
             Either (NVar nm outer) (NVar nm local)
locateNVar s (MkNVar {nvarIdx} p) = case choose (nvarIdx < size s) of
  Left so => Right (MkNVar (locateIsVarLT s so p))
  Right so => Left (MkNVar (locateIsVarGE s so p))

------------------------------------------------------------------------
-- Scope checking

export
isDeBruijn : Nat -> (vars : SnocList Name) -> Maybe (Var vars)
isDeBruijn Z (vs :< v) = pure (MkVar First)
isDeBruijn (S k) (vs :< _) = later <$> isDeBruijn k vs
isDeBruijn _ _ = Nothing

export
isNVar : (n : Name) -> (ns : SnocList Name) -> Maybe (NVar n ns)
isNVar n [<] = Nothing
isNVar n (ms :< m)
    = case nameEq n m of
           Nothing   => map later (isNVar n ms)
           Just Refl => pure (MkNVar First)

export
isVar : (n : Name) -> (ns : SnocList Name) -> Maybe (Var ns)
isVar n ns = forgetName <$> isNVar n ns

export
locateVar : SizeOf local -> Var (outer ++ local) ->
            Either (Var outer) (Var local)
locateVar s (MkVar {varIdx} p) = case choose (varIdx < size s) of
  Left so => Right (MkVar (locateIsVarLT s so p))
  Right so => Left (MkVar (locateIsVarGE s so p))

------------------------------------------------------------------------
-- Weakening

export
weakenNVar : SizeOf ns -> NVar name outer -> NVar name (outer ++ ns)
-- weakenNVar p x = case sizedView p of
--   Z     => x
--   (S p) => later (weakenNVar p x)
-- ^^^^ The above is the correct way, the below involves a proof which
-- is nonsense, but it's okay because it's deleted, and all we're doing is
-- adding a number so let's do it the quick way
weakenNVar s (MkNVar {nvarIdx} p)
  = MkNVar {nvarIdx = plus (size s) nvarIdx} (weakenIsVar s p)

export
insertNVar : SizeOf local ->
             NVar nm (outer ++ local) ->
             NVar nm (outer :< n ++ local)
insertNVar p v = case locateNVar p v of
  Left v => weakenNVar p (later v)
  Right (MkNVar p) => MkNVar (embedIsVar p)

export
insertNVarNames : GenWeakenable (NVar name)
insertNVarNames p q v = case locateNVar p v of
  Left v => rewrite sym $ appendAssociative outer ns local in weakenNVar (q + p) v
  Right (MkNVar p) => MkNVar (embedIsVar p)

export
insertVar : SizeOf local ->
            Var (outer ++ local) ->
            Var (outer :< n ++ local)
insertVar p (MkVar v) = forgetName $ insertNVar p (MkNVar v)

weakenVar : SizeOf ns -> Var outer -> Var (outer ++ ns)
weakenVar p (MkVar v) = forgetName $ weakenNVar p (MkNVar v)

insertVarNames : GenWeakenable Var
insertVarNames p q (MkVar v) = forgetName $ insertNVarNames p q (MkNVar v)

||| The (partial) inverse to insertVar
export
removeVar : SizeOf local ->
            Var        (outer :< x ++ local) ->
            Maybe (Var (outer      ++ local))
removeVar out var = case locateVar out var of
  Left (MkVar {varIdx = 0} _) => Nothing
  Left (MkVar {varIdx = S k} p) => pure (weakenVar out $ MkVar (dropLater p))
  Right (MkVar p) => pure (MkVar (embedIsVar p))

------------------------------------------------------------------------
-- Reindexing

compatIsVar : CompatibleVars xs ys ->
                 {idx : Nat} ->
                 (0 p : IsVar name idx xs) ->
                 Var ys
compatIsVar prf p = believe_me (MkVar p)
-- compatIsVar CompatPre First = (MkVar First)
-- compatIsVar (CompatExt x) First = (MkVar First)
-- compatIsVar CompatPre (Later p) = (MkVar (Later p))
-- compatIsVar (CompatExt y) (Later p)
--     = let (MkVar p') = compatIsVar y p in MkVar (Later p')

compatVar : CompatibleVars xs ys -> Var xs -> Var ys
compatVar prf (MkVar p) = compatIsVar prf p

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
Weaken (Var {a = Name}) where
  weaken = later
  weakenNs = weakenVar

export
FreelyEmbeddable (Var {a = Name}) where
  embed (MkVar p) = MkVar (embedIsVar p)

export
IsScoped (Var {a = Name}) where
  compatNs = compatVar

  thin (MkVar p) = thinIsVar p
  shrink (MkVar p) = shrinkIsVar p

export
Weaken (NVar {a = Name} nm) where
  weaken = later
  weakenNs = weakenNVar

export
FreelyEmbeddable (NVar {a = Name} nm) where
  embed (MkNVar p) = MkNVar (embedIsVar p)

------------------------------------------------------------------------
-- Used variables

||| This used to be a (Vect (length vars) Bool) which meant
||| we needed to keep a lot of `vars` around to be able to
||| pattern-match on it without first fording `length vars`
||| out. It was very annoying so it's now a hand-rolled type
||| even though that means we cannot use e.g. Vect's `replicate`.
export
data Used : Scoped where
  Lin : Used [<]
  (:<) : Used vars -> Bool -> Used (vars :< x)

%name Used bs, us

export
initUsed : {vars : Scope} -> Used vars
initUsed {vars = [<]} = [<]
initUsed {vars = (sx :< x)} = initUsed :< False

export
Weaken Used where
  weaken xs = xs :< False

export
tail : Used (vars :< x) -> Used vars
tail (xs :< _) = xs

export
drop : SizeOf local -> Used (vars ++ local) -> Used vars
drop s bs = case sizedView s of
  Z => bs
  S k => drop k (tail bs)

export
markUsed : {idx : _} -> (0 prf : IsVar x idx vars) ->
  Used vars -> Used vars
markUsed First (bs :< _) = bs :< True
markUsed (Later p) (bs :< b) = markUsed p bs :< b

||| Only retain the variables that are actually used
export
used : {vars : Scope} -> Used vars -> Scope
used {vars = [<]} [<] = [<]
used {vars = vars :< v} (bs :< b)
    = ifThenElse b (:< v) id
    $ used bs

export
allUsed : Used vars -> List (Var vars)
allUsed = go zero where

  go : SizeOf inner -> Used vs -> List (Var (vs <>< inner))
  go s [<] = []
  go s (bs :< b) = fishyVar s :: go (suc s) bs

export
usedIsVar :
  (us : Used vars) ->
  {idx : Nat} -> (0 p : IsVar nm idx vars) ->
  NVar nm (used us)
usedIsVar (bs :< False) First = assert_total $
  idris_crash "INTERNAL ERROR: Referenced variable marked as unused"
usedIsVar (bs :< True) First = MkNVar First
usedIsVar (bs :< False) (Later p) = usedIsVar (bs) p
usedIsVar (bs :< True) (Later p) = later (usedIsVar (bs) p)

export
usedNVar : (us : Used vars) -> NVar nm vars -> NVar nm (used us)
usedNVar us (MkNVar p) = usedIsVar us p

export
usedVar : (us : Used vars) -> Var vars -> Var (used us)
usedVar us (MkVar p) = forgetName $ usedIsVar us p

-- this is a terrible name
export
usedNVarContextual : SizeOf inner -> (us : Used vars) ->
  NVar nm (vars ++ inner) -> NVar nm (used us ++ inner)
usedNVarContextual s us v = case locateNVar s v of
  Left v => weakenNs s (usedNVar us v)
  Right v => embed v

export
usedVarContextual : SizeOf inner -> (us : Used vars) ->
  Var (vars ++ inner) -> Var (used us ++ inner)
usedVarContextual s us (MkVar p) = forgetName (usedNVarContextual s us (MkNVar p))
