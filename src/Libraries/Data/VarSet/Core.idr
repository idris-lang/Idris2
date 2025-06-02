module Libraries.Data.VarSet.Core

import Data.Bits

import Libraries.Data.NatSet

import Core.Name.Scoped
import Core.TT.Var

import Libraries.Data.SnocList.SizeOf

%default total

export
VarSet : Scoped
VarSet vars = NatSet

export %inline
empty : VarSet vs
empty = NatSet.empty

export %inline
elem : Var vs -> VarSet vs -> Bool
elem (MkVar {varIdx} _) = NatSet.elem varIdx

export %inline
elemNat : Nat -> VarSet vs -> Bool
elemNat v = NatSet.elem v

export %inline
isEmpty : VarSet vs -> Bool
isEmpty = NatSet.isEmpty

export %inline
size : VarSet vs -> Nat
size = NatSet.size

export %inline
insert : Var vs -> VarSet vs -> VarSet vs
insert (MkVar {varIdx} _) = NatSet.insert varIdx

export %inline
delete : Var vs -> VarSet vs -> VarSet vs
delete (MkVar {varIdx} _) = NatSet.delete varIdx

export %inline
full : SizeOf vs -> VarSet vs
full p = NatSet.allLessThan p.size

export %inline
intersection : VarSet vs -> VarSet vs -> VarSet vs
intersection = NatSet.intersection

export %inline
union : VarSet vs -> VarSet vs -> VarSet vs
union = NatSet.union

export %inline %unsafe
unsafeToList : VarSet vs -> List (Var vs)
unsafeToList = believe_me NatSet.toList

export %inline
toList : {vs : Scope} -> VarSet vs -> List (Var vs)
toList = mapMaybe (`isDeBruijn` vs) . NatSet.toList

-- Pop the zero (whether or not in the set) and shift all the
-- other positions by -1 (useful when coming back from under
-- a binder)
export %inline
dropFirst : VarSet (vs :< v) -> VarSet vs
dropFirst = NatSet.popZ

export %inline
dropInner : SizeOf inner -> VarSet (Scope.addInner vs inner) -> VarSet vs
dropInner p = NatSet.popNs p.size

export %hint
varSetFreelyEmbeddable : FreelyEmbeddable VarSet
varSetFreelyEmbeddable = MkFreelyEmbeddable id

export %hint
varSetWeaken : Weaken VarSet
varSetWeaken = MkWeaken NatSet.addZ (\ inn, vs => cast (cast {to = Integer} vs `shiftL` inn.size))
