module Core.TT.Subst

import Core.Name
import Core.Name.Scoped
import Core.TT.Var

import Data.SnocList

%default total

public export
data Subst : Scoped -> Scope -> Scoped where
  Nil : Subst tm [<] vars
  (::) : tm vars -> Subst tm ds vars -> Subst tm (ds :< d) vars

namespace Var

  export
  index : Subst tm ds vars -> Var ds -> tm vars
  index [] (MkVar p) impossible
  index (t :: _) (MkVar First) = t
  index (_ :: ts) (MkVar (Later p)) = index ts (MkVar p)

export
findDrop :
  (Var vars -> tm vars) ->
  SizeOf dropped ->
  Var (vars ++ dropped) ->
  Subst tm dropped vars ->
  tm vars
findDrop k s var sub = case locateVar s var of
  Left var => index sub var
  Right var => k var

export
find : Weaken tm =>
       (forall vars. Var vars -> tm vars) ->
       SizeOf outer -> SizeOf dropped ->
       Var ((vars ++ dropped) ++ outer) ->
       Subst tm dropped vars ->
       tm (vars ++ outer)
find k outer dropped var sub = case locateVar outer var of
  Left var => k (embed var)
  Right var => weakenNs outer (findDrop k dropped var sub)

public export
0 Substitutable : Scoped -> Scoped -> Type
Substitutable val tm
  = {0 outer, dropped, vars : Scope} ->
    SizeOf outer ->
    SizeOf dropped ->
    Subst val dropped vars ->
    tm ((vars ++ dropped) ++ outer) ->
    tm (vars ++ outer)
