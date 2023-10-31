module Core.TT.Var

import Core.Name
import Core.Name.Scoped

import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

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
0 embedIsVar : IsVar x idx xs -> IsVar x idx (outer ++ xs)
embedIsVar First = First
embedIsVar (Later p) = Later (embedIsVar p)

||| Throw in extra variables on the local end of the context.
||| This is slow so we ensure it's only used in a runtime irrelevant manner
0 weakenIsVar : (s : SizeOf ns) -> IsVar x idx xs -> IsVar x (size s + idx) (xs ++ ns)
weakenIsVar (MkSizeOf Z Z) p =  p
weakenIsVar (MkSizeOf (S k) (S l)) p =  Later (weakenIsVar (MkSizeOf k l) p)

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
Eq (Var xs) where
  v == w = varIdx v == varIdx w

||| Removing var 0, strengthening all the other ones
export
dropFirst : List (Var (vs :< n)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

export
Show (Var ns) where
  show v = show (varIdx v)

||| The (partial) inverse to insertVar
export
removeVar : SizeOf local ->
            Var        (outer :< x ++ local) ->
            Maybe (Var (outer      ++ local))
removeVar out var = case sizedView out of
  Z => case var of
          MkVar First     => Nothing
          MkVar (Later p) => Just (MkVar p)
  S out' => case var of
              MkVar First     => Just (MkVar First)
              MkVar (Later p) => later <$> removeVar out' (MkVar p)

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
insertNVar p v = case sizedView p of
  Z     => later v
  (S p) => case v of
    MkNVar First     => MkNVar First
    MkNVar (Later v) => later (insertNVar p (MkNVar v))

export
insertNVarNames : SizeOf local -> SizeOf ns ->
                  NVar name (outer         ++ local) ->
                  NVar name ((outer ++ ns) ++ local)
insertNVarNames p q v = case sizedView p of
  Z     => weakenNVar q v
  (S p) => case v of
    MkNVar First      => MkNVar First
    MkNVar (Later v') => later (insertNVarNames p q (MkNVar v'))

export
insertVar : SizeOf local ->
            Var (outer ++ local) ->
            Var (outer :< n ++ local)
insertVar p (MkVar v) = let MkNVar v' = insertNVar p (MkNVar v) in MkVar v'

weakenVar : SizeOf ns -> Var outer -> Var (outer ++ ns)
weakenVar p (MkVar v) = let MkNVar v' = weakenNVar p (MkNVar v) in MkVar v'

insertVarNames : SizeOf local -> SizeOf ns ->
                 Var (outer         ++ local) ->
                 Var ((outer ++ ns) ++ local)
insertVarNames p q (MkVar v) = let MkNVar v' = insertNVarNames p q (MkNVar v) in MkVar v'

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
strengthenIsVar : {idx : Nat} -> (0 p : IsVar name idx xs) ->
  Thin ys xs -> Maybe (Var ys)
strengthenIsVar prf Refl = Just (MkVar prf)
strengthenIsVar First (Drop p) = Nothing
strengthenIsVar (Later x) (Drop p)
    = do MkVar prf' <- strengthenIsVar x p
         Just (MkVar prf')
strengthenIsVar First (Keep p) = Just (MkVar First)
strengthenIsVar (Later x) (Keep p)
    = do MkVar prf' <- strengthenIsVar x p
         Just (MkVar (Later prf'))

------------------------------------------------------------------------
-- Putting it all together

export
IsScoped (Var {a = Name}) where
  embedNs _ (MkVar p) = MkVar (embedIsVar p)
  weaken = later
  weakenNs = weakenVar
  compatNs = compatVar

  thin (MkVar p) = thinIsVar p
  strengthen (MkVar p) = strengthenIsVar p
