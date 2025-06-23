module Core.WithData

import Core.Name
import Core.FC
import Core.TT
import public Libraries.Data.WithData
import Libraries.Text.Bounded


export
(.bind) :
    {n : Nat} ->
    (0 inRange : NameInRange "bind" fields === Just (n, BindingModifier)) =>
    WithData fields a -> BindingModifier
(.bind) = WithData.get "bind"

export
(.fc) : {n : Nat} ->
        (prf : NameInRange "fc" fields === Just (n, FC)) => WithData fields a -> FC
(.fc) = WithData.get "fc"

export
setFC : {n : Nat} ->
        (prf : NameInRange "fc" fields === Just (n, FC)) => FC ->
        WithData fields a -> WithData fields a
setFC fc = WithData.set "fc" fc @{prf}

export
(.doc) : {n : Nat} ->
         (prf : NameInRange "doc" fields === Just (n, String)) =>
         WithData fields a -> String
(.doc) = WithData.get "doc"

public export
FC' : KeyVal
FC' = "fc" :-: FC

public export
WithFC : Type -> Type
WithFC = WithData [ FC' ]

public export
Doc' : KeyVal
Doc' = "doc" :-: String

public export
Bind' : KeyVal
Bind' = "bind" :-: BindingModifier

public export
Rig' : KeyVal
Rig' = "rig" :-: RigCount

public export
Name' : KeyVal
Name' = "name" :-: Name

export
(.name) : {n : Nat} ->
          (prf : NameInRange "name" fields === Just (n, Name)) =>
          WithData fields a -> Name
(.name) = WithData.get "name" @{prf}

export
(.fcname) : {n : Nat} ->
            (prf : NameInRange "fcname" fields === Just (n, WithFC Name)) =>
            WithData fields a -> WithFC Name
(.fcname) = WithData.get "fcname" @{prf}

public export
WithName : Type -> Type
WithName = WithData [ Name', FC' ]

export
MkWithName : WithFC Name -> ty -> WithName ty
MkWithName x y = Mk [x.val, x.fc] y

public export
FCBind : Type -> Type
FCBind = WithData [ Bind', FC' ]

-- a constructor label
public export
TyName' : KeyVal
TyName' = "tyname" :-: FCBind Name

export
(.tyName) : {n : Nat} ->
            (prf : NameInRange "tyname" fields === Just (n, FCBind Name)) =>
            WithData fields a -> FCBind Name
(.tyName) = WithData.get "tyname" @{prf}

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

------------------------------------------------------------------------
||| A wrapper for a value with a file context.
public export
MkFCVal : FC -> ty -> WithFC ty
MkFCVal fc = Mk [fc]

||| Smart constructor for WithFC that uses EmptyFC as location
%inline export
NoFC : a -> WithFC a
NoFC = MkFCVal EmptyFC

%inline export
mapFC : (a -> b) -> WithFC a -> WithFC b
mapFC = mapData

%inline export
distribFC : WithFC (List a) -> List (WithFC a)
distribFC x = map (MkFCVal x.fc) x.val

%inline export
traverseFCMaybe : (a -> Maybe b) -> WithFC a -> Maybe (WithFC b)
traverseFCMaybe = traverseDataMaybe

export
(.withFC) : (o : OriginDesc) => WithBounds t -> WithFC t
x.withFC = MkFCVal x.toFC x.val

