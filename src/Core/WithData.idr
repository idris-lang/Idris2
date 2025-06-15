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

export
(.doc) : {fs : List Label} -> (prf : Find "doc" fs === Just String) => WithData fs a -> String
(.doc) = WithData.get "doc" String @{prf}

public export
FC' : Label
FC' = "fc" :-: FC

public export
Doc' : Label
Doc' = "doc" :-: String

public export
Bind' : Label
Bind' = "bind" :-: BindingModifier

public export
Rig' : Label
Rig' = "rig" :-: RigCount

public export
Name' : Label
Name' = "name" :-: Name

public export
AddFC : Type -> Type
AddFC = WithData [ FC' ]

public export
WithName : Type -> Type
WithName = WithData [ Name', FC' ]

export
MkWithName : WithFC Name -> ty -> WithName ty
MkWithName x y = Mk [x.val, x.fc] y

public export
FCBind : Type -> Type
FCBind = WithData [ Bind', FC' ]

public export
DocBindFC : Type -> Type
DocBindFC = WithData [ Doc', Bind', FC' ]

-- When location is unavailable, use `EmptyFC`
export
HasDefault FC where
  def = EmptyFC

-- When binding is not provided, the default is not binding
export
HasDefault BindingModifier where
  def = NotBinding

-- default doc string
export
HasDefault String where
  def = ""

export
{fs : _} -> (prf : Find "fc" fs === Just FC) => HasFC (WithData fs a) where
  (.getFC) = (.fc)

