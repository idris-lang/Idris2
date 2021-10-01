module Core.Case.Util

import Core.Case.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.Value

||| Given a normalised type, get all the possible constructors for that
||| type family, with their type, name, tag, and arity.
export
getCons : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Defs -> NF vars -> Core (List (NF [], Name, Int, Nat))
getCons defs (NTCon _ tn _ _ _)
    = case !(lookupDefExact tn (gamma defs)) of
           Just (TCon _ _ _ _ _ _ cons _) =>
                do cs' <- traverse addTy cons
                   pure (catMaybes cs')
           _ => throw (InternalError "Called `getCons` on something that is not a Type constructor")
  where
    addTy : Name -> Core (Maybe (NF [], Name, Int, Nat))
    addTy cn
        = do Just gdef <- lookupCtxtExact cn (gamma defs)
                  | _ => pure Nothing
             case (definition gdef, type gdef) of
                  (DCon t arity _, ty) =>
                        pure (Just (!(nf defs [] ty), cn, t, arity))
                  _ => pure Nothing
getCons defs _ = pure []

emptyRHS : FC -> CaseTree vars -> CaseTree vars
emptyRHS fc (Case idx el sc alts) = Case idx el sc (map emptyRHSalt alts)
  where
    emptyRHSalt : CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase n t args sc) = ConCase n t args (emptyRHS fc sc)
    emptyRHSalt (DelayCase c arg sc) = DelayCase c arg (emptyRHS fc sc)
    emptyRHSalt (ConstCase c sc) = ConstCase c (emptyRHS fc sc)
    emptyRHSalt (DefaultCase sc) = DefaultCase (emptyRHS fc sc)
emptyRHS fc (STerm i s) = STerm i (Erased fc False)
emptyRHS fc sc = sc

export
mkAlt : {vars : _} ->
        FC -> CaseTree vars -> (Name, Int, Nat) -> CaseAlt vars
mkAlt fc sc (cn, t, ar)
    = ConCase cn t (map (MN "m") (take ar [0..]))
              (weakenNs (map take) (emptyRHS fc sc))

export
tagIs : Int -> CaseAlt vars -> Bool
tagIs t (ConCase _ t' _ _) = t == t'
tagIs t (ConstCase _ _) = False
tagIs t (DelayCase _ _ _) = False
tagIs t (DefaultCase _) = True

