module Idris.Doc.Display

import Core.Env
import Core.Evaluate

import Idris.IDEMode.Holes

import Idris.Pretty
import Idris.Resugar
import Idris.Syntax
import Idris.Syntax.Views

%hide Symbols.equals

%default covering

export
displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (shortName : Bool) -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayType shortName (n, i, gdef)
  = maybe (do tm <- resugar Env.empty !(normaliseHoles Env.empty (type gdef))
              nm <- aliasName (fullname gdef)
              let nm = ifThenElse shortName (dropNS nm) nm
              let prig = prettyRig gdef.multiplicity
              let ann = showCategory id gdef
              pure (prig <+> ann (cast $ prettyOp True nm) <++> colon <++> pretty tm))
          (\num => prettyHole Env.empty n num (type gdef))
          (isHole gdef)
export
displayTerm : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              ClosedTerm ->
              Core (Doc IdrisSyntax)
displayTerm tm
  = do ptm <- resugar Env.empty !(normaliseHoles Env.empty tm)
       pure (pretty ptm)

export
displayClause : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                Clause ->
                Core (Doc IdrisSyntax)
displayClause (MkClause env lhs rhs)
  = do lhstm <- resugar env !(normaliseHoles env lhs)
       rhstm <- resugar env !(normaliseHoles env rhs)
       pure (prettyLHS lhstm <++> equals <++> pretty rhstm)

  where
    prettyLHS : IPTerm -> Doc IdrisSyntax
    prettyLHS (PRef _ op) = cast $ prettyOp True op.rawName
    prettyLHS t = pretty t

export
displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (shortName : Bool) -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayPats shortName (n, idx, gdef)
  = case definition gdef of
      Function _ _ _ pats =>
        do ty <- displayType shortName (n, idx, gdef)
           ps <- traverse (displayClause) (maybe [] id pats)
           pure (vsep (ty :: ps))
      _ => pure (pretty0 n <++> reflow "is not a pattern matching definition")

export
displayImpl : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayImpl (n, idx, gdef)
  = case definition gdef of
      Function _ ct _ (Just [MkClause env  _ rhs]) =>
        do rhstm <- resugar env !(normaliseHoles env rhs)
           let (_, args) = getFnArgs defaultKindedName rhstm
           defs <- get Ctxt
           pds <- map catMaybes $ for args $ \ arg => do
             let (_, expr) = underLams (unArg arg)
             let (PRef _ kn, _) = getFnArgs defaultKindedName expr
               | _ => pure Nothing
             log "doc.implementation" 20 $ "Got name \{show @{Raw} kn}"
             let (ns, DN dn nm) = splitNS (kn.fullName)
               | _ => do log "doc.implementation" 10 $ "Invalid name \{show @{Raw} kn}"
                         pure Nothing
             let nm = NS ns nm
             Just (idx, gdef) <- lookupCtxtExactI kn.fullName (gamma defs)
               | _ => do log "doc.implementation" 10 $ "Couldn't find \{show @{Raw} nm}"
                         pure Nothing
             pdef <- displayPats True (nm, idx, gdef)
             pure (Just pdef)
           pure (vcat $ intersperse "" pds)
      _ => pure (pretty0 n <++> reflow "is not an implementation definition")
