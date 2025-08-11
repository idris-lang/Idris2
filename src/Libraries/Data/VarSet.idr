module Libraries.Data.VarSet

import Data.Bits

import Libraries.Data.NatSet

import Core.Name
import Core.Name.Scoped
import Core.TT.Var

import Libraries.Data.List.SizeOf

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
isEmpty : VarSet vs -> Bool
isEmpty = NatSet.isEmpty

export %inline
size : VarSet vs -> Nat
size = NatSet.size

export %inline
insert : Var vs -> VarSet vs -> VarSet vs
insert (MkVar {varIdx} _) = NatSet.insert varIdx

export %inline
singleton : Var vs -> VarSet vs
singleton v = VarSet.insert v (VarSet.empty {vs})

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
dropFirst : VarSet (v :: vs) -> VarSet vs
dropFirst = NatSet.popZ

-- Add a 'new' Zero (not in the set) and shift all the
-- other positions by +1 (useful when going under a binder)
export %inline
weaken : VarSet vs -> VarSet (v :: vs)
weaken = NatSet.addZ

export %inline
weakenNs : SizeOf inner -> VarSet vs -> VarSet (inner ++ vs)
weakenNs inn vs = cast (cast {to = Integer} vs `shiftL` inn.size)

export
FreelyEmbeddable VarSet
