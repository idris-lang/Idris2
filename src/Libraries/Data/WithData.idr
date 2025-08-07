||| The WithData module combines a record and an arbitrary payload. The intended use is to
||| attach metadata to the payload.
module Libraries.Data.WithData

import public Data.List.Quantifiers
import public Data.List
import public Data.Maybe
import public Libraries.Data.Record

%hide Data.List.Quantifiers.Any.Any
%hide Data.List.Quantifiers.Any.any

||| A pair for a type and an attached record hosting metadata about that type
|||
||| Intended usage
||| --------------
||| Only ever put plain types in the metadata
||| Do not add functors such as `List` or `PTerm`. The functor instance
||| for `WithData` is only functorial on its payload and not the metadata.
|||
||| There is rarely any need to write down `WithData [ ... ] a` thanks to the
||| `AddMetadata` type constructor.
|||
||| While possible, you are not meant to pattern match on values of this type
||| to extract the main payload, you can use the `val` projection, and to access
||| metadata fields you can use `get` and `getAt` functions that will automatically
||| compute and extract the value out of the metadata record.
|||
||| Example usage
||| -------------
||| Given a value of type `value : WithData ["loc" :-: Location, "cached" :-: Bool] Term`
||| we can access the `Term` by projecting our the underlying value:
||| ```idris example
||| termValue : Term
||| termValue = value.val
||| ```
||| To access the metadata fields use `get` with the name of the field or `getAt` with
||| the index of the field. For example "loc" is at index `0` therefore one can access
||| it using `getAt 0`:
||| ```idris example
||| termLocation : Location
||| termLocation = value `getAt` 0
||| ```
||| Similarly, we can obtain the "cached" field by giving its name directly
||| ```idris example
||| termCache : Bool
||| termCache = value.get "cached"
||| ```
public export
record WithData (additional : List KeyVal) (payload : Type) where
  constructor MkWithData
  metadata : Record additional
  val : payload

||| Add some metadata to a type given a label and a type for the metadata
||| This function matches on the type and add it to the metadata record if it is alread a `WithData`
|||
||| example:
||| ```idris example
||| Term : Type
|||
||| RichTerm : Type
||| RichTerm = AddMetadata ("loc" :-: Location) $ AddMetadata ("cached" :-: Bool) Term
||| ```
||| The example shows how to add the fields "loc" and "cached" to the type `Term` as metadata. Those
||| fields can be accessed with `get` and `getAt` functions
public export
AddMetadata : KeyVal -> Type -> Type
AddMetadata lbl (WithData ls a) = WithData (lbl :: ls) a
AddMetadata lbl ty = WithData [lbl] ty

||| Obtain the value of the metadata at the given index
||| @ ix The index of the value we are extracting
||| @ inRange A proof the index is in range of the metadata record
export
getAt : (ix : Nat) ->
        (0 inRange : FindIndex ix fields === Just out) =>
        WithData fields a -> out
getAt ix rec = index rec.metadata ix

||| Obtain the value out of the payload record given its label, same as `(.get)`
||| @ label The label of the value we are extracting
||| @ inRange A proof that the label is in the record at the appropriate index with the appropriate type.
export
get :
    (0 label : String) ->
    -- ^ The field we are accessing
    {n : Nat} ->
    -- ^ The index of the field, this can usually be infered
    (0 inRange : NameInRange label fields === Just (n, out)) =>
    -- ^ A proof that the field is in the record, its position matches the index `n` and the type at that location is `out`
    WithData fields a ->
    -- ^ The data from which we are extracting the field
    out
get label rec = Record.get label rec.metadata

||| Obtain the value out of the payload record given its label, same as `get`.
||| @ label The label of the value we are extracting.
||| @ inRange A proof that the label is in the record at the appropriate index with the appropriate type.
export
(.get) :
    WithData fields a ->
    -- ^ The data from which we are extracting the field
    (0 field : String) ->
    -- ^ The field we are accessing
    {n : Nat} ->
    -- ^ The index of the field, this can usually be infered
    (0 inRange : NameInRange field fields === Just (n, out)) =>
    -- ^ A proof that the field is in the record, its position matches the index `n` and the type at that location is `out`
    out
(.get) rec field = Record.get field rec.metadata

||| Update at the given index, updates cannot change the type of the field.
||| @ ix The index at which we update the value.
||| @ inRange A proof that the index is in range of the metadata record.
||| @ f The update function.
export
updateAt :
    (ix : Nat) ->
    -- ^ The index selected for updating
    (inRange : FindIndex ix fields === Just out) =>
    -- ^ The proof that the index is in range
    (f : out -> out) ->
    -- ^ The update function.
    WithData fields a -> WithData fields a
updateAt ix f = {metadata $= updateAt ix f}

||| Update the value with the given field name
||| @ label The label of the value we are updating
||| @ inRange A proof that the label is in the record at the appropriate index with the appropriate type.
||| @ f The update function.
export
update :
    (0 label : String) ->
    -- ^ The field we want to update
    {n : Nat} ->
    -- ^ The index of the field, this can usually be infered
    (0 inRange : NameInRange label fields === Just (n, out)) =>
    -- ^ A proof that the field is in the record, its position matches the index `n` and the type at that location is `out`
    (f : out -> out) ->
    -- ^ The update function for the field
    WithData fields a ->
    -- ^ The data for which we are updating the field
    WithData fields a
update label f = {metadata $= update label f}

||| Override the value at the given index.
||| @ n The index at which we replace our value.
||| @ inRange A proof that index is in range.
||| @ newVal The new value remplacing the existing one.
export
setAt :
    (n : Nat) ->
    -- ^ The index at which we override our value
    (inRange : FindIndex n ls === Just out) =>
    -- ^ A proof that the index is in range
    (newVal : out) ->
    -- ^ The new value that is going to replace the old one
    WithData ls a ->
    -- ^ The data for which we are overriding a value
    WithData ls a
setAt n v = {metadata $= setAt n v}

||| Override the value matching the given label
||| @ label The label of the value we are overriding.
||| @ inRange A proof that the label is in the record at the appropriate index with the appropriate type.
||| @ newVal The new value remplacing the existing one.
export
set :
    (0 label : String) -> {n : Nat} ->
    (0 inRange : NameInRange label ls === Just (n, out)) =>
    (newVal : out) ->
    WithData ls a -> WithData ls a
set label val = {metadata $= Record.set label val}


||| Add a labelled value to the metadata
export
Add : (0 lbl : String) -> (_ : ty) -> a -> WithData [lbl :-: ty] a
Add lbl ty x = MkWithData [ lbl :- ty ] x

||| Add value the payload, ignore the label since it's given by the type
export
(:+) : ty -> WithData ls a -> WithData (lbl :-: ty :: ls) a
val :+ x = MkWithData (add lbl val x.metadata) x.val

export infixr 8 :++

||| Drop the head element of the metadata
export
drop : WithData (l :: ls) a -> WithData ls a
drop = {metadata $= Record.tail }

||| Drop the head element of the metadata
export
(.drop) : WithData (l :: ls) a -> WithData ls a
(.drop) = {metadata $= Record.tail }

||| WithData is functiorial in its payload
export
Functor (WithData md) where
  map f x = MkWithData x.metadata (f x.val)

------------------------------------------------------------------------------------------------
-- Default fields for records
------------------------------------------------------------------------------------------------

||| An interface for default values, used to fill in missing values in metadata records
public export
interface HasDefault a | a where
  defValue : a

fromDefault : All (HasDefault . KeyVal.type) fs -> Record fs
fromDefault [] = []
fromDefault (_ :: y) = ? :- defValue :: fromDefault y

||| Construct a payload filled with default values for its metadata
export
MkDef : {fs : _} -> a -> (values : All (HasDefault . KeyVal.type) fs) => WithData fs a
MkDef x = MkWithData ((fromDefault values)) x

||| Construct a value with metadata but ignore the labels
export
Mk : {fs : _} -> All KeyVal.type fs -> a -> WithData fs a
Mk x y = MkWithData (fromElems x) y

||| Add a default value to an existing metadata record
export
AddDef :  (def : HasDefault ty) =>
         WithData fl a -> WithData (lbl :-: ty :: fl) a
AddDef x = (defValue @{def}) :+ x

------------------------------------------------------------------------------------------------
-- WithData distributes with List and Maybe
------------------------------------------------------------------------------------------------

export
distribData : WithData fs (List a) -> List (WithData fs a)
distribData x = map (MkWithData x.metadata) x.val

export
distribDataMaybe : WithData fs (Maybe a) -> Maybe (WithData fs a)
distribDataMaybe (MkWithData metadata Nothing) = Nothing
distribDataMaybe (MkWithData metadata (Just x)) = Just (MkWithData metadata x)

export
traverseDataMaybe : (a -> Maybe b) -> WithData fs a -> Maybe (WithData fs b)
traverseDataMaybe f x = MkWithData x.metadata <$> f x.val

------------------------------------------------------------------------------------------------
-- Interface implementations
------------------------------------------------------------------------------------------------

export
(eq : All (Eq . KeyVal.type) fs) => Eq (Record fs) where
  (==) [] [] = True
  (==) {eq = e :: es} {fs = (f :: fs)} (x :: xs) (y :: ys) = x.value == y.value && xs == ys

export
(eq : All (Eq . KeyVal.type) fs) => Eq a => Eq (WithData fs a) where
  x == y = x.val == y.val && x.metadata == y.metadata

