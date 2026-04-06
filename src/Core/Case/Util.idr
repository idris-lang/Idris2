module Core.Case.Util

import Core.Case.CaseTree
import Core.Context
import Core.Evaluate.Value

import Parser.Rule.Source

import Data.SnocList

import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.Extra

public export
record DataCon where
  constructor MkDataCon
  name  : Name
  tag   : Int
  arity : Nat
  quantities : List RigCount

||| Given a normalised type, get all the possible constructors for that
||| type family, with their type, name, tag, and arity.
export
getCons : Defs -> NF vars -> Core (List DataCon)
getCons defs (VTCon fc tn _ _)
    = if is_primitive
        then -- This a primitive type, so nothing to add (we
             -- can't generate all the possibilities after all!)
             pure []
        else
          case !(lookupDefExact tn (gamma defs)) of
              Just (TCon _ _ _ _ _ cons _) =>
                    do cs' <- traverse addTy (fromMaybe [] cons)
                       pure (catMaybes cs')
              x => throw (InternalError "Called `getCons` on something that is not a Type constructor: \{show tn} of \{show x}")
  where
    is_primitive : Bool
    is_primitive = case tn of
      UN (Basic n) => elem n reservedNames
      _ => False

    addTy : Name -> Core (Maybe DataCon)
    addTy cn
        = do Just gdef <- lookupCtxtExact cn (gamma defs)
                  | _ => pure Nothing
             case (gdef.definition, gdef.type) of
                  (DCon di t arity, ty) =>
                        pure . Just $ MkDataCon cn t arity (quantities di)
                  _ => pure Nothing
getCons defs _ = pure []

emptyRHS : FC -> CaseTree vars -> CaseTree vars
emptyRHS _ (TCase cfc c idx el sc alts) = TCase cfc c idx el sc (map emptyRHSalt alts)
  where
    emptyRHSscope : forall vars . FC -> TCaseScope vars -> TCaseScope vars
    emptyRHSscope fc (TRHS tm) = TRHS (emptyRHS fc tm)
    emptyRHSscope fc (TArg c x sc) = TArg c x (emptyRHSscope fc sc)

    emptyRHSalt : TCaseAlt vars -> TCaseAlt vars
    emptyRHSalt (TConCase fc n t sc) = TConCase fc n t (emptyRHSscope fc sc)
    emptyRHSalt (TDelayCase fc c arg sc) = TDelayCase fc c arg (emptyRHS fc sc)
    emptyRHSalt (TConstCase fc c sc) = TConstCase fc c (emptyRHS fc sc)
    emptyRHSalt (TDefaultCase fc sc) = TDefaultCase fc (emptyRHS fc sc)
emptyRHS fc (STerm i fs s) = STerm i fs (Erased fc Placeholder)
emptyRHS _ sc = sc

export
mkAlt : FC -> CaseTree vars -> DataCon -> TCaseAlt vars
mkAlt fc sc (MkDataCon cn t ar qs)
    = TConCase fc cn t (mkScope qs (map (MN "m") (take ar [0..])))
  where
    mkScope : List RigCount -> SnocList Name -> TCaseScope vars
    mkScope _ [<] = TRHS (emptyRHS fc sc)
    mkScope [] (vs :< v) = TArg top v (weaken (mkScope [] vs))
    mkScope (q :: qs) (vs :< v) = TArg q v (weaken (mkScope qs vs))

emptyRHSTm : FC -> Term vars -> Term vars
emptyRHSTm fc (Case cfc ct c sc scTy alts)
    = Case cfc ct c sc scTy (map emptyRHSalt alts)
  where
    emptyRHSscope : forall vars . FC -> CaseScope vars -> CaseScope vars
    emptyRHSscope fc (RHS fs tm) = RHS fs (emptyRHSTm fc tm)
    emptyRHSscope fc (Arg c x sc) = Arg c x (emptyRHSscope fc sc)

    emptyRHSalt : forall vars . CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase fc n t sc) = ConCase fc n t (emptyRHSscope fc sc)
    emptyRHSalt (DelayCase fc c arg sc) = DelayCase fc c arg (emptyRHSTm fc sc)
    emptyRHSalt (ConstCase fc c sc) = ConstCase fc c (emptyRHSTm fc sc)
    emptyRHSalt (DefaultCase fc sc) = DefaultCase fc (emptyRHSTm fc sc)
emptyRHSTm fc tm@(Unmatched _ _) = tm
emptyRHSTm fc _ = Erased fc Placeholder

export
mkAltTm : {vars : _} ->
        FC -> Term vars -> DataCon -> CaseAlt vars
mkAltTm fc sc (MkDataCon cn t ar qs)
    = ConCase fc cn t (mkScope zero qs (map (MN "m") (take ar [0..])))
  where
    mkScope : SizeOf more -> List RigCount -> SnocList Name ->
              CaseScope (vars ++ more)
    mkScope s _ [<] = RHS [] (weakenNs s (emptyRHSTm fc sc))
    mkScope s [] (vs :< v) = Arg top v (mkScope (suc s) [] vs)
    mkScope s (q :: qs) (vs :< v) = Arg q v (mkScope (suc s) qs vs)

export
tagIs : Int -> TCaseAlt vars -> Bool
tagIs t (TConCase _ _ t' _) = t == t'
tagIs t (TConstCase _ _ _) = False
tagIs t (TDelayCase _ _ _ _) = False
tagIs t (TDefaultCase _ _) = True

export
tagIsTm : Int -> CaseAlt vars -> Bool
tagIsTm t (ConCase _ _ t' _) = t == t'
tagIsTm t (ConstCase _ {}) = False
tagIsTm t (DelayCase _ {}) = False
tagIsTm t (DefaultCase _ _) = True
