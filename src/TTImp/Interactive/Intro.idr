module TTImp.Interactive.Intro

import Core.Core
import Core.Context
import Core.Env
import Core.Metadata
import Core.TT
import Core.TT.Views
import Core.Unify

import Idris.Desugar
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Unelab
import TTImp.Utils

%default covering

parameters
  {lhsCtxt : _ }
  {auto c : Ref Ctxt Defs}
  {auto s : Ref Syn SyntaxInfo}
  {auto m : Ref MD Metadata}
  {auto u : Ref UST UState}
  {auto r : Ref ROpts REPLOpts}
  (hidx : Int)
  (hole : Name)
  (env : Env Term lhsCtxt)

  introLam : Name -> RigCount -> Term lhsCtxt -> Core IRawImp
  introLam x rig ty = do
    ty <- unelab env ty
    defs <- get Ctxt
    new_hole <- uniqueHoleName defs [] (nameRoot hole)
    let iintrod = ILam replFC rig Explicit (Just x) ty (IHole replFC new_hole)
    pure iintrod

  introCon : Name -> Term lhsCtxt -> Core (Maybe IRawImp)
  introCon n ty = do
    defs <- get Ctxt
    Just gdef <- lookupCtxtExact n (gamma defs)
      | _ => pure Nothing
    -- for now we only handle types with a unique constructor
    let TCon _ _ _ _ _ _ [cons] _ = definition gdef
      | _ => pure Nothing
    Just gdef <- lookupCtxtExact cons (gamma defs)
      | _ => pure Nothing
    let n = lengthExplicitPi $ fst $ snd $ underPis (-1) [] (type gdef)
    ns <- uniqueHoleNames defs n (nameRoot hole)
    let new_holes = PHole replFC True <$> ns
    let pcons = papply replFC (PRef replFC cons) new_holes
    -- We're desugaring it to the corresponding TTImp
    icons <- desugar AnyExpr lhsCtxt pcons
    let gty = gnf env ty
    ccons <- checkTerm hidx {-is this correct?-} InExpr [] (MkNested []) env icons gty
    defs <- get Ctxt
    ncons <- normaliseHoles defs env ccons
    icons <- unelab env ncons
    pure $ Just icons

  export
  intro : Term lhsCtxt -> Core (Maybe IRawImp)
  -- structural cases
  intro (Bind _ x (Let _ _ ty val) sc) = intro (subst val sc)
  intro (TDelayed _ _ t) = intro t
  -- interesting ones
  intro (Bind _ x (Pi _ rig Explicit ty) _) = Just <$> introLam x rig ty
  intro t = case getFnArgs t of
    (Ref _ (TyCon _ ar) n, _) => introCon n t
    _ => pure Nothing
