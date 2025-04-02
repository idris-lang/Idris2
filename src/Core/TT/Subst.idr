module Core.TT.Subst

import Core.Name
import Core.Name.Scoped
import Core.TT.Var

import Data.List
import Data.SnocList

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf

%default total

-- TODO replace by pointwise lifting: `Subst tm ds vars = All (\_. tm vars) ds`
public export
data Subst : Scoped -> Scope -> Scoped where
  Nil : Subst tm Scope.empty vars
  (::) : tm vars -> Subst tm ds vars -> Subst tm (d :: ds) vars

public export
empty : Subst tm Scope.empty vars
empty = []


namespace Var

  export
  index : Subst tm ds vars -> Var ds -> tm vars
  index [] (MkVar p) impossible
  index (t :: _) (MkVar First) = t
  index (_ :: ts) (MkVar (Later p)) = index ts (MkVar p)

-- TODO revisit order of `dropped` and `Subst`
export
findDrop :
  (Var vars -> tm vars) ->
  SizeOf dropped ->
  Var (dropped ++ vars) ->
  Subst tm dropped vars ->
  tm vars
findDrop k s var sub = case locateVar s var of
  Left var => index sub var
  Right var => k var

export
find : Weaken tm =>
       (forall vars. Var vars -> tm vars) ->
       SizeOf outer -> SizeOf dropped ->
       Var (outer ++ (dropped ++ vars)) ->
       Subst tm dropped vars ->
       tm (outer ++ vars)
find k outer dropped var sub = case locateVar outer var of
  Left var => k (embed var)
  Right var => weakenNs outer (findDrop k dropped var sub)

-- TODO rename `outer`
public export
0 Substitutable : Scoped -> Scoped -> Type
Substitutable val tm
  = {0 outer, dropped, vars : Scope} ->
    SizeOf outer ->
    SizeOf dropped ->
    Subst val dropped vars ->
    tm (outer ++ (dropped ++ vars)) ->
    tm (outer ++ vars)
