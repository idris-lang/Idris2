module Libraries.Data.WithData

import public Data.List.Quantifiers
import public Data.List

%hide Data.List.Quantifiers.Any.Any
%hide Data.List.Quantifiers.Any.any

export infixr 9 :-:
export infix 9 :-
export infixr 9 :+

||| A type with a string-description for it. Used in `Record`
public export
record KeyVal where
  constructor (:-:)
  label : String
  type : Type

||| The value-constructor for `KeyVal`
public export
record LabelledValue (kv : KeyVal) where
  constructor (:-)
  0 label : String
  {auto 0 check : kv.label === label}
  val : kv.type

||| A labelled heterogenous list
public export
Record : List KeyVal -> Type
Record = All LabelledValue

||| Build a record from it's element values ignoring the labels
export
fromElems : {fs : _} -> All KeyVal.type fs -> Record fs
fromElems {fs = []} [] = []
fromElems {fs = (l :-: t :: xs)} (x :: zs) = (l :- x) :: fromElems zs

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

||| A procedure to find the type associated with a label
public export
Find : String -> List KeyVal -> Maybe Type
Find str [] = Nothing
Find str (x :: xs) = if str == x.label then Just x.type else Find str xs

namespace Record
  ||| Add a label and a value to a record
  export
  Add : (0 str : String) -> (_ : ty) -> Record ls -> Record (str :-: ty :: ls)
  Add str val xs = (str :- val) :: xs

  ||| Obtain the value from a record given its label and the first instance of it in the record
  export
  get : {ls : List KeyVal} -> (field : String) -> (prf : Find field ls === Just out) => Record ls -> out
  get {ls = []} field csx = absurd prf
  get {ls = ((str :-: ty) :: xs)} field (x :: z) {prf} with (field == str)
    get {ls = ((str :-: ty) :: xs)} field (x :: z) {prf} | False = get field {ls = xs} z
    get {ls = ((str :-: ty) :: xs)} field (x :: z) {prf = Refl}| True = val x

  ||| Obtain the value from a record given its label and type
  export
  get' : {ls : List KeyVal} -> (field : String) -> (0 out : Type) -> (prf : Find field ls === Just out) => Record ls -> out
  get' {ls = []} field out x = absurd prf
  get' {ls = ((label :-: type) :: xs)} field out x {prf} with (field == label)
    get' {ls = ((label :-: type) :: xs)} field out (x :: y) {prf} | False = get' field out y
    get' {ls = ((label :-: out) :: xs)} field out (x :: y) {prf = Refl} | True = val x

  ||| Update the value at the given label
  export
  set : {ls : List KeyVal} -> (field : String) -> (v : out) -> (prf : Find field ls === Just out) => Record ls -> Record ls
  set {ls = []} field v x = absurd prf
  set {ls = ((label :-: type) :: xs)} field {out} v x {prf} with (field == label)
    set {ls = ((label :-: type) :: xs)} field {out} v (x :: y) {prf} | False = x :: set field v y
    set {ls = ((label :-: out) :: xs)} field  {out} v (x :: y) {prf = Refl} | True = (label :- v) :: y

  export
  update : {fs : List KeyVal} -> (field : String) -> (f : out -> out) ->
           (prf : Find field fs === Just out) => Record fs -> Record fs
  update field f x = set field (f $ get field x) x

||| Obtain the value out of the payload record given its label
export
get : {ls : List KeyVal} -> (field : String) -> (0 out : Type) -> (prf : Find field ls === Just out) => WithData ls a -> out
get field out = Record.get' field out . extra

||| Set the value in the payload given its label
export
set : {ls : List KeyVal} -> (field : String) -> (val : out) -> (prf : Find field ls === Just out) => WithData ls a -> WithData ls a
set field val = {extra $= Record.set field val}

export
update : {fs : List KeyVal} -> (field : String) -> (f : out -> out) ->
         (prf : Find field fs === Just out) => WithData fs a -> WithData fs a
update field f x = WithData.set field (f $ WithData.get field out x) x

||| Add value the payload, ignore the label since it's given by the type
export
(:+) : ty -> WithData ls a -> WithData (lbl :-: ty :: ls) a
val :+ x = MkWithData (Add lbl val x.extra) x.val

export infixr 8 :++

||| Add a record to the payload
export
(:++) : Record ls -> WithData xs a -> WithData (ls ++ xs) a
(:++) rec x = MkWithData (rec ++ x.extra) x.val

export
drop : WithData (l :: ls) a -> WithData ls a
drop = {extra $= tail}

export
(.drop) : WithData (l :: ls) a -> WithData ls a
(.drop) = {extra $= tail}

namespace Blank

  export
  Add : (0 lbl : String) -> (_ : ty) -> a -> WithData [lbl :-: ty] a
  Add lbl ty x = MkWithData [ lbl :- ty ] x

public export
AddTy : KeyVal -> Type -> Type
AddTy lbl (WithData ls a) = WithData (lbl :: ls) a
AddTy lbl ty = WithData [lbl] ty

export
mapData : forall extra. (a -> b) -> WithData extra a -> WithData extra b
mapData f x = MkWithData x.extra (f x.val)

public export
interface HasDefault a | a where
  def : a

fromDefault : All (HasDefault . KeyVal.type) fs -> Record fs
fromDefault [] = []
fromDefault (_ :: y) = ? :- def :: fromDefault y

||| construct a payload filled with default values
export
MkDef : {fs : _} -> a -> (values : All (HasDefault . KeyVal.type) fs) => WithData fs a
MkDef x = MkWithData ((fromDefault values)) x

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

