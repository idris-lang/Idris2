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
-- Arity information
------------------------------------------------------------------------------------------
||| function arity
public export
Arity' : KeyVal
Arity' = "arity" :-: Nat

public export
WithArity : Type -> Type
WithArity = AddMetadata Arity'

||| Obtain arity information from the metadata
export
(.arity) :
    {n : Nat} ->
    (0 inRange : NameInRange "arity" fields === Just (n, Nat)) =>
    WithData fields a -> Nat
(.arity) = WithData.get "arity"

------------------------------------------------------------------------------------------
-- Options information
------------------------------------------------------------------------------------------
||| data constructor options
public export
Opts' : KeyVal
Opts' = "opts" :-: List DataOpt

public export
WithOpts : Type -> Type
WithOpts = AddMetadata Opts'

||| Obtain data options from the metadata
export
(.opts) :
    {n : Nat} ->
    (0 inRange : NameInRange "opts" fields === Just (n, List DataOpt)) =>
    WithData fields a -> List DataOpt
(.opts) = WithData.get "opts"

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

public export
AddFC : Type -> Type
AddFC = AddMetadata FC'

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

export
(.addFC) : (o : OriginDesc) => WithBounds (WithData ls t) -> WithData (FC' :: ls) t
(.addFC) x = x.toFC :+ x.val

------------------------------------------------------------------------------------------
-- Helpers for documentation information
------------------------------------------------------------------------------------------

||| The "doc" label containing documentation information for metadata records
public export
Doc' : KeyVal
Doc' = "doc" :-: String

public export
WithDoc : Type -> Type
WithDoc = AddMetadata Doc'

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

public export
WithRig : Type -> Type
WithRig = AddMetadata Rig'

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

||| Extract the name out of the metadata.
export
(.nameVal) : {n : Nat} ->
          (inRange : NameInRange "name" fields === Just (n, WithFC Name)) =>
          WithData fields a -> Name
(.nameVal) x = x.name.val

||| Attach name and file context information to a type
public export
WithName : Type -> Type
WithName = AddMetadata Name'

||| the "tyname" label containing a `WithFC Name` for metadata records. Typically used for type names.
public export
TyName' : KeyVal
TyName' = "tyname" :-: WithFC Name

||| Extract the "tyname" value from the metadata record
export
(.tyName) : {n : Nat} ->
            (inRange : NameInRange "tyname" fields === Just (n, WithFC Name)) =>
            WithData fields a -> WithFC Name
(.tyName) = WithData.get "tyname" @{inRange}


||| Attach documentation, binding and location information to a type
public export
DocBindFC : Type -> Type
DocBindFC = WithData [ Doc', Bind', FC' ]

||| the "mname" label containing a `Maybe (WithFC Name)` for metadata records
public export
MName' : KeyVal
MName' = "mname" :-: Maybe (WithFC Name)

public export
WithMName : Type -> Type
WithMName = AddMetadata MName'

export
(.mName) : {n : Nat} ->
            (inRange : NameInRange "mname" fields === Just (n, Maybe (WithFC Name))) =>
            WithData fields a -> Maybe (WithFC Name)
(.mName) = WithData.get "mname" @{inRange}

||| the "names" label containing a `List (WithFC Name)` for metadata records
public export
Names' : KeyVal
Names' = "names" :-: List (WithFC Name)

public export
WithNames : Type -> Type
WithNames = AddMetadata Names'

export
(.names) : {n : Nat} ->
            (inRange : NameInRange "names" fields === Just (n, List (WithFC Name))) =>
            WithData fields a -> List (WithFC Name)
(.names) = WithData.get "names" @{inRange}

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

