module Core.TT.Subst

import Core.Name.Scoped
import Core.TT.Var

import Data.SnocList
import Data.SnocList.Quantifiers

import Libraries.Data.SnocList.SizeOf

%default total

public export
-- TODO revisit order of ds and vars?
-- TODO vars is constantly applied
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

export
findDrop :
  (Var outer -> tm outer) ->
  SizeOf dropped ->
  Var (Scope.addInner outer dropped) ->
  Subst tm dropped outer ->
  tm outer
findDrop k s var sub = case locateVar s var of
  Left var => k var
  Right var => lookup sub var

export
find : Weaken tm =>
       (forall vars. Var vars -> tm vars) ->
       SizeOf dropped ->
       SizeOf inner ->
       Var (Scope.addInner (Scope.addInner outer dropped) inner) ->
       Subst tm dropped outer ->
       tm (Scope.addInner outer inner)
find k dropped inner var sub = case locateVar inner var of
  Left var => weakenNs inner (findDrop {tm} k dropped var sub)
  Right var => k (embed var)

public export
0 Substitutable : Scoped -> Scoped -> Type
Substitutable val tm
  = {0 outer, dropped, inner : Scope} ->
    SizeOf dropped ->
    SizeOf inner ->
    Subst val dropped outer ->
    tm (Scope.addInner (Scope.addInner outer dropped) inner) ->
    tm (Scope.addInner outer inner)
