module Core.TT.Subst

import Core.Name.Scoped
import Core.TT.Var

import Data.SnocList
import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf

%default total

public export
Subst : Scoped -> Scope -> Scoped
Subst tm ds vars = All (\_ => tm vars) ds

export
cons : Subst tm ds vars -> tm vars -> Subst tm (v `cons` ds) vars
cons [<] p = Lin :< p
cons (ns :< s) p = cons ns {tm} p :< s

namespace Subst
  public export
  empty : Subst tm Scope.empty vars
  empty = [<]

  public export
  bind : Subst tm ds vars -> tm vars -> Subst tm (Scope.bind ds v) vars
  bind = (:<)

namespace Var

  export
  index : Subst tm ds vars -> Var ds -> tm vars
  index [<] (MkVar p) impossible
  index (_ :< t) (MkVar First) = t
  index (ts :< _) (MkVar (Later p)) = index ts {tm} (MkVar p)

-- TODO revisit order of `dropped` and `Subst`
export
findDrop :
  (Var vars -> tm vars) ->
  SizeOf dropped ->
  Var (Scope.addInner vars dropped) ->
  Subst tm dropped vars ->
  tm vars
findDrop k s var sub = case locateVar s var of
  Left var => index sub {tm} var
  Right var => k var

export
find : Weaken tm =>
       (forall vars. Var vars -> tm vars) ->
       SizeOf outer -> SizeOf dropped ->
       Var (Scope.addInner (Scope.addInner vars dropped) outer) ->
       Subst tm dropped vars ->
       tm (Scope.addInner vars outer)
find k outer dropped var sub = case locateVar outer var of
  Left var => k (embed var)
  Right var => weakenNs outer (findDrop k {tm} dropped var sub)

-- TODO rename `outer`
public export
0 Substitutable : Scoped -> Scoped -> Type
Substitutable val tm
  = {0 outer, dropped, vars : Scope} ->
    SizeOf outer ->
    SizeOf dropped ->
    Subst val dropped vars ->
    tm (Scope.addInner (Scope.addInner vars dropped) outer) ->
    tm (Scope.addInner vars outer)
