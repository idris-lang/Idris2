||| Level is to Var
||| what Local is to Scope

-- TODO: rename Var to Index?

module Core.TT.Level

import Data.Nat
import Data.SnocList
import Data.Vect

import Core.Name
import Core.Name.Scoped

import Libraries.Data.List.HasLength
import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.HasLength
import Libraries.Data.SnocList.SizeOf

import Libraries.Data.Erased
import Libraries.Data.SnocList.Extra

%default total

------------------------------------------------------------------------
-- IsLevel Predicate

||| IsLevel n k ns is a proof that
||| the name n
||| is a position k
||| in the snoclist ns
public export
data IsLevel : a -> Nat -> List a -> Type where
     First : IsLevel n Z (n :: ns)
     Later : IsLevel n i ns -> IsLevel n (S i) (m :: ns)

%name IsLevel idx

export
finIdx : {idx : _} -> (0 prf : IsLevel x idx vars) ->
         Fin (length vars)
finIdx First = FZ
finIdx (Later l) = FS (finIdx l)

namespace IsLevel

  ||| Recover the value pointed at by an IsLevel proof
  export
  nameAt : {vars : List a} -> {idx : Nat} -> (0 p : IsLevel n idx vars) -> a
  nameAt {vars = n :: _} First = n
  nameAt (Later p) = nameAt p

||| Inversion principle for Later
export
dropLater : IsLevel nm (S idx) (v :: vs) -> IsLevel nm idx vs
dropLater (Later p) = p

export
appendIsLevel : HasLength m inner -> IsLevel nm m (inner ++ nm :: outer)
appendIsLevel Z = First
appendIsLevel (S x) = Later (appendIsLevel x)

export
chippyIsLevel : HasLength m inner -> IsLevel nm m (inner <>> nm :: outer)
chippyIsLevel hl
  = rewrite chipsAsListAppend inner (nm :: outer) in
    appendIsLevel
  $ rewrite sym $ plusZeroRightNeutral m in
    hlChips hl Z

||| Compute the remaining scope once the target level has been removed
public export
dropIsLevel :
  (ns : List a) ->
  {idx : Nat} -> (0 p : IsLevel name idx ns) ->
  List a
dropIsLevel (_ :: xs) First = xs
dropIsLevel (n :: xs) (Later p) = n :: dropIsLevel xs p

------------------------------------------------------------------------
-- Level in scope

||| A variable in a scope is a name, a De Bruijn level,
||| and a proof that the name is at that position in the Local.
||| Everything but the De Bruijn index is erased.
public export
record Level (vars : List a) where
  constructor MkLevel
  {levelIdx : Nat}
  {0 levelNm : a}
  0 levelPrf : IsLevel levelNm levelIdx vars

namespace Level

  export
  later : Level ns -> Level (n :: ns)
  later (MkLevel p) = MkLevel (Later p)

  ||| Recover the value pointed at by an Level proof
  export
  nameAt : {vars : List a} -> Level vars -> a
  nameAt (MkLevel p) = nameAt p

export
appendLevel : SizeOf inner -> Level (inner ++ nm :: outer)
appendLevel (MkSizeOf s p) = MkLevel (appendIsLevel p)

export
chippyLevel : SizeOf inner -> Level (inner <>> nm :: outer)
chippyLevel (MkSizeOf s p) = MkLevel (chippyIsLevel p)

export
dropLevel : {ns : List a} -> Level ns -> List a
dropLevel (MkLevel p) = dropIsLevel ns p

------------------------------------------------------------------------
-- Named level in scope

public export
record NLevel (nm : a) (vars : List a) where
  constructor MkNLevel
  {nlevelIdx : Nat}
  0 nlevelPrf : IsLevel nm nlevelIdx vars

namespace NLevel
  export
  later : NLevel nm ns -> NLevel nm (n :: ns)
  later (MkNLevel p) = MkNLevel (Later p)

  ||| Recover the value pointed at by an NLevel proof
  export
  nameAt : {vars : List a} -> NLevel nm vars -> a
  nameAt (MkNLevel p) = nameAt p

export
forgetName : NLevel nm vars -> Level vars
forgetName (MkNLevel p) = MkLevel p

export
recoverName : (lvl : Level vars) -> NLevel (levelNm lvl) vars
recoverName (MkLevel p) = MkNLevel p

public export
dropNLevel : {ns : List a} -> NLevel nm ns -> List a
dropNLevel (MkNLevel p) = dropIsLevel ns p

export
appendNLevel : SizeOf inner -> NLevel nm (inner ++ nm :: outer)
appendNLevel (MkSizeOf s p) = MkNLevel (appendIsLevel p)

export
chippyNLevel : SizeOf inner -> NLevel nm (inner <>> nm :: outer)
chippyNLevel (MkSizeOf s p) = MkNLevel (chippyIsLevel p)
