module TTImp.Interactive.Intro

import Core.Env
import Core.Metadata
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

import Data.SnocList

import Libraries.Data.NatSet

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

  introCon : Name -> Term lhsCtxt -> Core (List IRawImp)
  introCon n ty = do
    defs <- get Ctxt
    ust <- get UST
    Just gdef <- lookupCtxtExact n (gamma defs)
      | _ => pure []
    -- for now we only handle types with a unique constructor
    let TCon _ _ _ _ _ cs _ = definition gdef
      | _ => pure []
    let gty = gnf env ty
    ics <- for (fromMaybe [] cs) $ \ cons => do
      Just gdef <- lookupCtxtExact cons (gamma defs)
        | _ => pure Nothing
      let nargs = lengthExplicitPi $ fst $ snd $ underPis (-1) Env.empty (type gdef)
      new_hole_names <- uniqueHoleNames defs nargs (nameRoot hole)
      let new_holes = PHole replFC True <$> new_hole_names
      let pcons = papply replFC (PRef replFC cons) new_holes
      res <- catch
        (do -- We're desugaring it to the corresponding TTImp
            icons <- desugar AnyExpr (toList lhsCtxt) pcons
            ccons <- checkTerm hidx {-is this correct?-} InExpr [] (NestedNames.empty) env icons gty
            newdefs <- get Ctxt
            ncons <- normaliseHoles newdefs env ccons
            icons <- unelab env ncons
            pure (Just icons))
        (\ _ => pure Nothing)
      put Ctxt defs -- reset the context, we don't want any updates
      put UST ust
      pure res
    pure (catMaybes ics)

  export
  intro : Term lhsCtxt -> Core (List IRawImp)
  -- structural cases
  intro (Bind _ x (Let _ _ ty val) sc) = toList <$> intro (subst val sc)
  intro (TDelayed _ _ t) = intro t
  -- interesting ones
  intro (Bind _ x (Pi _ rig Explicit ty) _) = pure <$> introLam x rig ty
  intro t = case getFnArgs t of
    (Ref _ (TyCon ar) n, _) => introCon n t
    _ => pure []
