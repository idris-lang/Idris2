module Libraries.Data.VarSet

-- If we had defined these functions in the same file as `VarSet`,
-- we would see a lot of unsolved metas because `VarSet` computes
-- away to `NatSet`.
-- Hence the split between (unsafe, bit-manipulating) `.Core`
-- primitive definitions and type-safe derived notions

import Core.Name.Scoped
import Core.TT.Var

import Libraries.Data.SnocList.SizeOf

import public Libraries.Data.VarSet.Core as VarSet

%default total

export %inline
singleton : Var vs -> VarSet vs
singleton v = insert v Core.empty

export %inline
append : SizeOf inner -> VarSet inner -> VarSet outer ->
         VarSet (addInner outer inner)
append p inn out = union (embed {tm = VarSet} inn) (weakenNs {tm = VarSet} p out)

export
fromVarSet : (vars : Scope) -> VarSet vars -> (newvars ** Thin newvars vars)
fromVarSet [<] xs = (Scope.empty ** Refl)
fromVarSet (ns :< n) xs =
    let (_ ** svs) = fromVarSet ns (VarSet.dropFirst xs) in
    if first `VarSet.elem` xs
      then (_ ** Keep svs)
      else (_ ** Drop svs)

-- If it was constructed from SnocList-like structure
export %inline
asList : {vs : Scope} -> VarSet vs -> List (Var vs)
asList = reverse . Core.toList
