module Core.WithData

import Core.Name
import Core.FC
import Core.TT
import public Libraries.Data.WithData

export
(.name) : {fs : List Label} -> (prf : Find "name" fs === Just Name) => WithData fs a -> Name
(.name) = WithData.get "name" Name @{prf}

export
(.bind) : {fs : List Label} -> (prf : Find "bind" fs === Just BindingModifier) => WithData fs a -> BindingModifier
(.bind) = WithData.get "bind" BindingModifier @{prf}

export
(.fc) : {fs : List Label} -> (prf : Find "fc" fs === Just FC) => WithData fs a -> FC
(.fc) = WithData.get "fc" FC @{prf}

public export
AddFC : Type -> Type
AddFC = WithData ["fc" :-: FC]

public export
FCName : Type -> Type
FCName = WithData [ "fc" :-: FC, "name" :-: Name ]

public export
FCBind : Type -> Type
FCBind = WithData [ "fc" :-: FC, "bind" :-: BindingModifier]

export
HasDefault FC where
  def = EmptyFC

export
{fs : _} -> (prf : Find "fc" fs === Just FC) => HasFC (WithData fs a) where
  (.getFC) = (.fc)

