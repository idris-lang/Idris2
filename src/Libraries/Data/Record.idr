||| Modular records based on `All`
module Libraries.Data.Record

import public Data.List.Quantifiers
import Data.Maybe

%hide Data.List.Quantifiers.Any.Any
%hide Data.List.Quantifiers.Any.any

export infixr 9 :-:
export infix 9 :-
export infixr 9 :+

||| A type with a string-label for it. Used in `Record`
|||
||| ```idris example
||| IntLabel : KeyVal
||| IntLabel = "int" :-: Int
||| ```
public export
record KeyVal where
  constructor (:-:)
  label : String
  type : Type

||| The value-constructor for `KeyVal`, essentially a pair of a label
||| and a value that match the specification given by `KeyVal`
|||
||| ```idris example
||| IntLabel : KeyVal
||| IntLabel = "int" :-: Int
|||
||| intValue : LabelledValue IntLabel
||| intValue = "int" :- 3
||| ```
public export
record LabelledValue (kv : KeyVal) where
  constructor (:-)
  ||| The label matching the `KeyVal` spec, erased for performance reasons
  0 label : String
  ||| A proof that the label given matches the label in the specification
  {auto 0 check : kv.label === label}
  ||| A runtime value of the type given by the specification
  value : kv.type

||| Records are a list of of labelled values, their fields are given by a list of KeyVal
||| Each element in the list describes a key
|||
||| ```idris example
||| Spec : List KeyVal
||| Spec = [ "username" :-: String, "amount" :-: Double ]
|||
||| recordValue : Record Spec
||| recordValue = [ "username" :- "Alice", "amount" :- 3.14 ]
||| ```
public export
Record : (fields : List KeyVal) -> Type
Record = All LabelledValue

||| Build a record from it's element values ignoring the labels
|||
||| ```idris example
||| Spec : List KeyVal
||| Spec = [ "username" :-: String, "amount" :-: Double ]
|||
||| recordValue : Record Spec
||| recordValue = fromElems [ "Alice", 3.14 ]
||| ```
export
fromElems : {fs : _} -> All KeyVal.type fs -> Record fs
fromElems {fs = []} [] = []
fromElems {fs = (l :-: t :: xs)} (x :: zs) = (l :- x) :: fromElems zs

||| Obtain the tail of a list of predicates
export
tail : All p (x :: xs) -> All p xs
tail (_ :: xs) = xs

||| A procedue to find the type at the given index
public export 0
FindIndex : Nat -> List KeyVal -> Maybe Type
FindIndex Z (x :: xs) = Just x.type
FindIndex (S n) (x :: xs) = FindIndex n xs
FindIndex _ _ = Nothing

||| A procedure to find the index and type of a given label
public export 0
NameInRange : (key : String) -> List KeyVal -> Maybe (Nat, Type)
NameInRange key [] = Nothing
NameInRange key (x :: xs) = if (key == x.label)
                               then Just (Z, x.type)
                               else map (mapFst S) (NameInRange key xs)

-- Convert a `NameInRange` proof to a `FindIndex` proof
0
IndexInRange : {fields : List KeyVal} ->
               NameInRange key fields === Just (ix, ty) ->
               FindIndex ix fields === Just ty
IndexInRange {fields = []} prf = absurd prf
IndexInRange {fields = ((label :-: type) :: xs)} {ty} prf with (key == label)
  IndexInRange {fields = ((label :-: type) :: xs)} {ty} prf | False with (NameInRange key xs) proof p
    IndexInRange {fields = ((label :-: type) :: xs)} {ty} prf | False | Nothing = absurd prf
    IndexInRange {fields = ((label :-: type) :: xs)} {ty} Refl | False | (Just (x, ty))
      = IndexInRange {fields = xs, key} p
  IndexInRange {fields = ((label :-: type) :: xs)} {ty = type} Refl | True = Refl

||| Add a label and a value to a record
export
add : (0 str : String) -> (_ : ty) -> Record fields -> Record (str :-: ty :: fields)
add str val xs = (str :- val) :: xs

absurd0 : (0 _ : t) -> Uninhabited t => a
absurd0 x = void (uninhabited x)

||| Obtain the value from a record at given index
||| @ n The index at which we extract the value.
||| @ out The type of the value at the index.
||| @ inRange A proof that the field is in the record at the appropriate index with the appropriate type.
export
index : Record fields -> (n : Nat) -> (0 inRange : FindIndex n fields === Just out) => out
index ((label :- val) :: y) 0 {inRange = Refl} = val
index (x :: y) (S k) = index y k
index [] 0 = absurd0 inRange
index [] (S k) = absurd0 inRange

||| Obtain the value from a record given its label.
||| @ field The field for which we extract the value.
||| @ n The index corresponding to the field given.
||| @ out The type of the value at the given field.
||| @ inRange A proof that the field is in the record at the appropriate index with the appropriate type.
export
get : (0 label : String) -> Record fields ->
      {n : Nat} ->
      (0 inRange : NameInRange label fields === Just (n, out)) => out
get field rec = index rec n {inRange = IndexInRange inRange}

||| Obtain the value from a record given its label and type.
||| @ field The field for which we extract the value.
||| @ out The type of the value at the given field.
||| @ n The index corresponding to the field given.
||| @ inRange A proof that the field is in the record at the appropriate index with the appropriate type.
export
get' : (0 label : String) -> (0 out : Type) -> Record fields ->
       {n : Nat} ->
       (0 inRange : NameInRange label fields === Just (n, out)) =>
       out
get' label type rec = get {n} label {out = type} rec {inRange = inRange}

||| Remove a value from the list, used in the type of `removeAt`
public export
ListRemoveAt :
    (fields : List KeyVal) -> (n : Nat) ->
    (inRange : IsJust (FindIndex n fields)) => List KeyVal
ListRemoveAt [] 0 = absurd inRange
ListRemoveAt (x :: xs) 0 = xs
ListRemoveAt [] (S k) = absurd inRange
ListRemoveAt (x :: xs) (S k) = x :: ListRemoveAt xs k

||| Remove the value at the given index.
||| @ n The index we are removing.
||| @ inRange A proof that the index is in range of the record spec.
export
removeAt :
    (n : Nat) ->
    (inRange : IsJust (FindIndex n fields)) =>
    Record fields -> Record (ListRemoveAt fields n)
removeAt 0 [] = absurd inRange
removeAt 0 (x :: z) = z
removeAt (S k) [] = absurd inRange
removeAt (S k) (x :: xs) = x :: removeAt k xs

||| Update the value at the given index.
||| @ n The index we are removing.
||| @ inRange A proof that the index is in range of the record spec.
||| @ f The update function.
export
updateAt :
    (n : Nat) ->
    (0 inRange : (FindIndex n fields) === Just out) =>
    (f : out -> out) ->
    Record fields -> Record fields
updateAt 0 f [] = absurd0 inRange
updateAt 0 f ((label :- val) :: y) {inRange = Refl} = label :- f val :: y
updateAt (S k) f [] = absurd0 inRange
updateAt (S k) f (x :: y) = x :: updateAt k f y

||| Update the value with the given label.
||| @ field The label of the value we are updating.
||| @ inRange A proof that the label is in the record at the appropriate index with the appropriate type.
||| @ f The update function.
export
update :
    (0 label : String) -> {n : Nat} ->
    (0 inRange : NameInRange label fields === Just (n, out)) =>
    (f : out -> out) ->
    Record fields -> Record fields
update field f rec = updateAt n {fields, out, inRange = IndexInRange inRange} f rec

||| Override the value found at the given index.
||| @ n The index we are removing.
||| @ inRange A proof that the index is in range of the record spec.
||| @ newVal The value that will replace the existing one.
export
setAt : (n : Nat) -> (inRange : FindIndex n fields === Just out) => (newVal : out) ->
        Record fields -> Record fields
setAt n newVal x = updateAt n (const newVal) x


||| Override the value found at the given label.
||| @ label The label of the value we are overriding.
||| @ inRange A proof that the label is in the record at the appropriate index with the appropriate type.
||| @ newVal The value that will replace the existing one.
export
set :
    (0 label : String) -> {n : Nat} ->
    (0 inRange : NameInRange label fields === Just (n, out)) =>
    (newVal : out) ->
    Record fields -> Record fields
set field newVal rec = update field (const newVal) rec
