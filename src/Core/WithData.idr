module Core.WithData

import Core.Name
import Core.FC
import Core.TT
import public Libraries.Data.WithData
import Libraries.Text.Bounded

------------------------------------------------------------------------------------------
-- Helpers for binding information
------------------------------------------------------------------------------------------

||| The "bind" label containing binding information for metadata records
public export
Bind' : KeyVal
Bind' = "bind" :-: BindingModifier

||| Obtain binding information from the metadata
export
(.bind) :
    {n : Nat} ->
    (0 inRange : NameInRange "bind" fields === Just (n, BindingModifier)) =>
    WithData fields a -> BindingModifier
(.bind) = WithData.get "bind"

------------------------------------------------------------------------------------------
-- Totality information
------------------------------------------------------------------------------------------

||| The "totalReq" label containing totality information for metadata records
public export
Tot' : KeyVal
Tot' = "totalReq" :-: Maybe TotalReq

||| Obtain totality information from the metadata
export
(.totReq) :
    {n : Nat} ->
    (0 inRange : NameInRange "totalReq" fields === Just (n, Maybe TotalReq)) =>
    WithData fields a -> Maybe TotalReq
(.totReq) = WithData.get "totalReq"

------------------------------------------------------------------------------------------
-- Helpers for FC information
------------------------------------------------------------------------------------------

||| The "fc" label containing file context information for metadata records
public export
FC' : KeyVal
FC' = "fc" :-: FC

||| Attach FC information to a type
public export
WithFC : Type -> Type
WithFC = WithData [ FC' ]

||| Obtain file context information from the metadata
export
(.fc) : {n : Nat} ->
        (inRange : NameInRange "fc" fields === Just (n, FC)) => WithData fields a -> FC
(.fc) = WithData.get "fc"

export
setFC : {n : Nat} ->
        (inRange : NameInRange "fc" fields === Just (n, FC)) => FC ->
        WithData fields a -> WithData fields a
setFC fc = WithData.set "fc" fc @{inRange}

||| Attach binding and file context information to a type
public export
FCBind : Type -> Type
FCBind = WithData [ Bind', FC' ]

||| A wrapper for a value with a file context.
public export
MkFCVal : FC -> ty -> WithFC ty
MkFCVal fc = Mk [fc]

||| Smart constructor for WithFC that uses EmptyFC as location
%inline export
NoFC : a -> WithFC a
NoFC = MkFCVal EmptyFC

export
(.withFC) : (o : OriginDesc) => WithBounds t -> WithFC t
x.withFC = MkFCVal x.toFC x.val

------------------------------------------------------------------------------------------
-- Helpers for documentation information
------------------------------------------------------------------------------------------

||| The "doc" label containing documentation information for metadata records
public export
Doc' : KeyVal
Doc' = "doc" :-: String

||| Obtain documentation information from the metadata
export
(.doc) : {n : Nat} ->
         (inRange : NameInRange "doc" fields === Just (n, String)) =>
         WithData fields a -> String
(.doc) = WithData.get "doc"

------------------------------------------------------------------------------------------
-- Helpers for quantity information
------------------------------------------------------------------------------------------

||| The "rig" label containing quantity information for metadata records
public export
Rig' : KeyVal
Rig' = "rig" :-: RigCount

||| Obtain quantity information from the metadata
export
(.rig) : {n : Nat} ->
         (inRange : NameInRange "rig" fields === Just (n, RigCount)) =>
         WithData fields a -> RigCount
(.rig) = WithData.get "rig"

------------------------------------------------------------------------------------------
-- Helpers for name information
------------------------------------------------------------------------------------------

||| The "name" label containing a `Name` for metadata records
public export
Name' : KeyVal
Name' = "name" :-: WithFC Name


||| Extract the name out of the metadata.
export
(.name) : {n : Nat} ->
          (inRange : NameInRange "name" fields === Just (n, WithFC Name)) =>
          WithData fields a -> WithFC Name
(.name) = WithData.get "name" @{inRange}

||| Attach name and file context information to a type
public export
WithName : Type -> Type
WithName = WithData [ Name']

||| Smart constructor to add a name and location to a type
export
MkWithName : WithFC Name -> ty -> WithName ty
MkWithName x y = Mk [x] y

||| the "tyname" label containing a `FCBind Name` for metadata records
public export
TyName' : KeyVal
TyName' = "tyname" :-: FCBind Name

||| Extract the "tyname" value from the metadata record
export
(.tyName) : {n : Nat} ->
            (inRange : NameInRange "tyname" fields === Just (n, FCBind Name)) =>
            WithData fields a -> FCBind Name
(.tyName) = WithData.get "tyname" @{inRange}


||| Attach documentation, binding and location information to a type
public export
DocBindFC : Type -> Type
DocBindFC = WithData [ Doc', Bind', FC' ]

------------------------------------------------------------------------
-- Default instances for metadata
------------------------------------------------------------------------

-- When location is unavailable, use `EmptyFC`
export
HasDefault FC where
  defValue = EmptyFC

-- When binding is not provided, the default is not binding
export
HasDefault BindingModifier where
  defValue = NotBinding

-- default doc string
export
HasDefault String where
  defValue = ""

------------------------------------------------------------------------

