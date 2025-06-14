module Libraries.Data.WithData

import public Data.List.Quantifiers
import public Data.List

export infixr 9 :-:
export infix 9 :-
export infix 9 :+

public export
record Label where
  constructor (:-:)
  label : String
  type : Type

public export
record DataLabel (str : String) (ty : Type) where
  constructor (:-)
  0 label : String
  {auto 0 check : str === label}
  val : ty

public export
data Record : (fields : List Label) -> Type where
  Nil : Record []
  (::) : DataLabel str ty -> Record ls -> Record (str :-: ty :: ls)

export
fromElems : {fs : _} -> All Label.type fs -> Record fs
fromElems {fs = []} [] = []
fromElems {fs = (l :-: t :: xs)} (x :: zs) = (l :- x) :: fromElems zs

public export
record WithData (additional : List Label) (payload : Type) where
  constructor MkWithData
  extra : Record additional
  val : payload

public export
Find : String -> List Label -> Maybe Type
Find str [] = Nothing
Find str (x :: xs) = if str == x.label then Just x.type else Find str xs

namespace Record
  export
  Add : (0 str : String) -> (_ : ty) -> Record ls -> Record (str :-: ty :: ls)
  Add str val xs = (str :- val) :: xs

  export
  get : {ls : List Label} -> (field : String) -> (prf : Find field ls === Just out) => Record ls -> out
  get {ls = []} field csx = absurd prf
  get {ls = ((str :-: ty) :: xs)} field (x :: z) {prf} with (field == str)
    get {ls = ((str :-: ty) :: xs)} field (x :: z) {prf} | False = get field {ls = xs} z
    get {ls = ((str :-: ty) :: xs)} field (x :: z) {prf = Refl}| True = val x

  export
  get' : {ls : List Label} -> (field : String) -> (out : Type) -> (prf : Find field ls === Just out) => Record ls -> out
  get' {ls = []} field out x = absurd prf
  get' {ls = ((label :-: type) :: xs)} field out x {prf} with (field == label)
    get' {ls = ((label :-: type) :: xs)} field out (x :: y) {prf} | False = get' field out y
    get' {ls = ((label :-: out) :: xs)} field out (x :: y) {prf = Refl} | True = val x

  export
  set : {ls : List Label} -> (field : String) -> (v : out) -> (prf : Find field ls === Just out) => Record ls -> Record ls
  set {ls = []} field v x = absurd prf
  set {ls = ((label :-: type) :: xs)} field {out} v x {prf} with (field == label)
    set {ls = ((label :-: type) :: xs)} field {out} v (x :: y) {prf} | False = x :: set field v y
    set {ls = ((label :-: out) :: xs)} field  {out} v (x :: y) {prf = Refl} | True = (label :- v) :: y

export
get : {ls : List Label} -> (field : String) -> (out : Type) -> (prf : Find field ls === Just out) => WithData ls a -> out
get field out = Record.get' field out . extra

export
set : {ls : List Label} -> (field : String) -> (val : out) -> (prf : Find field ls === Just out) => WithData ls a -> WithData ls a
set field val = {extra $= Record.set field val}

export
(:+) : DataLabel lbl ty -> WithData ls a -> WithData (lbl :-: ty :: ls) a
((:-) lbl val {check = Refl}) :+ x = MkWithData (Add lbl val x.extra) x.val

namespace Blank

  export
  Add : (lbl : String) -> (_ : ty) -> a -> WithData [lbl :-: ty] a
  Add lbl ty x = MkWithData [ lbl :- ty ] x

export
mapData : forall extra. (a -> b) -> WithData extra a -> WithData extra b
mapData f x = MkWithData x.extra (f x.val)

public export
interface HasDefault a | a where
  def : a

fromAll : {fs : _} -> HList (map Label.type fs) ->  Record fs
fromAll {fs = []} x = []
fromAll {fs = (f :-: t :: ys)} (x :: xs) = (? :- x) :: fromAll xs

fromDefault : All (HasDefault . Label.type) fs -> HList (map Label.type fs)
fromDefault [] = []
fromDefault (_ :: y) = def :: fromDefault y

export
make : {fs : _} -> a -> (values : All (HasDefault . Label.type) fs) => WithData fs a
make x = MkWithData (fromAll (fromDefault values)) x

export
Mk : {fs : _} -> All Label.type fs -> a -> WithData fs a
Mk x y = MkWithData (fromElems x) y

export
distribData : WithData fs (List a) -> List (WithData fs a)
distribData x = map (MkWithData x.extra) x.val

export
traverseDataMaybe : (a -> Maybe b) -> WithData fs a -> Maybe (WithData fs b)
traverseDataMaybe f x = MkWithData x.extra <$> f x.val

