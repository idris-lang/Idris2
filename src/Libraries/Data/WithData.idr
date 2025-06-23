||| The WithData module combines a record and an arbitrary payload. The intended use is to
||| attach metadata to the payload.
module Libraries.Data.WithData

import public Data.List.Quantifiers
import public Data.List
import public Data.Maybe
import public Libraries.Data.Record

%hide Data.List.Quantifiers.Any.Any
%hide Data.List.Quantifiers.Any.any

||| A pair of a type and an arbitrary payload given by a record
|||
||| Only ever put plain types in the extra data
||| do not add functors such as `List` or `PTerm`. The functor instance
||| for `WithData` is only functorial on its payload and not the additional
||| data.
public export
record WithData (additional : List KeyVal) (payload : Type) where
  constructor MkWithData
  extra : Record additional
  val : payload

export
getAt : (ix : Nat) -> (0 inRange : FindIndex ix fields === Just out) =>
        WithData fields a-> out
getAt ix rec = index rec.extra ix

||| Obtain the value out of the payload record given its label
export
get : (0 field : String) ->  {n : Nat} ->
      (0 inRange : NameInRange field fields === Just (n, out)) =>
      WithData fields a -> out
get field rec = Record.get field rec.extra

||| Update at the given index, updates cannot change the type of the field
export
updateAt :
    (ix : Nat) ->
    -- ^ The index selected for updating
    (prf : FindIndex ix fields === Just out) =>
    -- ^ The proof that the index is in range
    (f : out -> out) ->
    -- ^ The update function.
    WithData fields a -> WithData fields a
updateAt ix f = {extra $= updateAt ix f}

||| Update the value with the given field name
export
update :
    (0 field : String) ->
    -- ^ The field name we want to update
    {n : Nat} ->
    -- ^ its index in the list
    (0 sameNat : NameInRange field fields === Just (n, out)) =>
    -- ^ A proof that the index is in range of the record
    (f : out -> out) ->
    -- ^ The update function for the field
    WithData fields a -> WithData fields a
update field f = {extra $= update field f}

||| Override the value at the given index by the one given in argument.
export
setAt :
    (n : Nat) -> (prf : FindIndex n ls === Just out) => (newVal : out) ->
    WithData ls a -> WithData ls a
setAt n v = {extra $= setAt n v}

||| Override the value matching the given label
export
set :
    (0 field : String) -> {n : Nat} ->
    (0 inRange : NameInRange field ls === Just (n, out)) =>
    (newVal : out) ->
    WithData ls a -> WithData ls a
set field val = {extra $= Record.set field val}


||| Add a labelled value to the payload
export
Add : (0 lbl : String) -> (_ : ty) -> a -> WithData [lbl :-: ty] a
Add lbl ty x = MkWithData [ lbl :- ty ] x

||| Add value the payload, ignore the label since it's given by the type
export
(:+) : ty -> WithData ls a -> WithData (lbl :-: ty :: ls) a
val :+ x = MkWithData (add lbl val x.extra) x.val

export infixr 8 :++

||| Add a record to the payload
export
(:++) : Record ls -> WithData xs a -> WithData (ls ++ xs) a
(:++) rec x = MkWithData (rec ++ x.extra) x.val

||| Drop the head element of the metadata
export
drop : WithData (l :: ls) a -> WithData ls a
drop = {extra $= Record.tail }

||| Drop the head element of the metadata
export
(.drop) : WithData (l :: ls) a -> WithData ls a
(.drop) = {extra $= Record.tail }

namespace Blank

||| Add some metadata to a type
||| This function matches on the type and add it to the metadata record if it is alread a `WithData`
public export
AddTy : KeyVal -> Type -> Type
AddTy lbl (WithData ls a) = WithData (lbl :: ls) a
AddTy lbl ty = WithData [lbl] ty

||| WithData is functiorial in its payload
export
mapData : forall extra. (a -> b) -> WithData extra a -> WithData extra b
mapData f x = MkWithData x.extra (f x.val)

------------------------------------------------------------------------------------------------
-- Default fields for records
------------------------------------------------------------------------------------------------
public export
interface HasDefault a | a where
  def : a

fromDefault : All (HasDefault . KeyVal.type) fs -> Record fs
fromDefault [] = []
fromDefault (_ :: y) = ? :- def :: fromDefault y

||| Construct a payload filled with default values for its metadata
export
MkDef : {fs : _} -> a -> (values : All (HasDefault . KeyVal.type) fs) => WithData fs a
MkDef x = MkWithData ((fromDefault values)) x

||| Construct a value with metadata but ignore the labels
export
Mk : {fs : _} -> All KeyVal.type fs -> a -> WithData fs a
Mk x y = MkWithData (fromElems x) y

export
AddDef : {fs : _} -> (values : All (HasDefault . KeyVal.type) fs) =>
         WithData fl a -> WithData (fs ++ fl) a
AddDef x = fromDefault values :++ x

export
distribData : WithData fs (List a) -> List (WithData fs a)
distribData x = map (MkWithData x.extra) x.val

export
distribDataMaybe : WithData fs (Maybe a) -> Maybe (WithData fs a)
distribDataMaybe (MkWithData extra Nothing) = Nothing
distribDataMaybe (MkWithData extra (Just x)) = Just (MkWithData extra x)

export
traverseDataMaybe : (a -> Maybe b) -> WithData fs a -> Maybe (WithData fs b)
traverseDataMaybe f x = MkWithData x.extra <$> f x.val

export
(eq : All (Eq . KeyVal.type) fs) => Eq (Record fs) where
  (==) [] [] = True
  (==) {eq = e :: es} {fs = (f :: fs)} (x :: xs) (y :: ys) = x.val == y.val && xs == ys

export
(eq : All (Eq . KeyVal.type) fs) => Eq a => Eq (WithData fs a) where
  x == y = x.val == y.val && x.extra == y.extra

