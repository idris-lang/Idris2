module Idris.Doc.Display

import Core.Case.CaseTree
import Core.Context
import Core.Env

import Data.String

import Idris.IDEMode.Holes

import Idris.Pretty
import Idris.Resugar
import Idris.Syntax
import Idris.Syntax.Views

import Libraries.Text.PrettyPrint.Prettyprinter.Util

%default covering

export
displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (shortName : Bool) -> Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayType shortName defs (n, i, gdef)
  = maybe (do tm <- resugar [] !(normaliseHoles defs [] (type gdef))
              nm <- aliasName (fullname gdef)
              let nm = ifThenElse shortName (dropNS nm) nm
              let prig = prettyRig gdef.multiplicity
              let ann = showCategory id gdef
              pure (prig <+> ann (prettyOp nm) <++> colon <++> prettyTerm tm))
          (\num => prettyHole defs [] n num (type gdef))
          (isHole gdef)
export
displayTerm : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> ClosedTerm ->
              Core (Doc IdrisSyntax)
displayTerm defs tm
  = do ptm <- resugar [] !(normaliseHoles defs [] tm)
       pure (prettyTerm ptm)

export
displayClause : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                Defs -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core (Doc IdrisSyntax)
displayClause defs (vs ** (env, lhs, rhs))
  = do lhstm <- resugar env !(normaliseHoles defs env lhs)
       rhstm <- resugar env !(normaliseHoles defs env rhs)
       pure (prettyTerm lhstm <++> keyword equals <++> prettyTerm rhstm)

export
displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (shortName : Bool) -> Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayPats shortName defs (n, idx, gdef)
  = case definition gdef of
      PMDef _ _ _ _ pats =>
        do ty <- displayType shortName defs (n, idx, gdef)
           ps <- traverse (displayClause defs) pats
           pure (vsep (ty :: ps))
      _ => pure (pretty n <++> reflow "is not a pattern matching definition")

export
displayImpl : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayImpl defs (n, idx, gdef)
  = case definition gdef of
      PMDef _ _ ct _ [(vars ** (env,  _, rhs))] =>
        do rhstm <- resugar env !(normaliseHoles defs env rhs)
           let (_, args) = getFnArgs rhstm
           defs <- get Ctxt
           pds <- map catMaybes $ for args $ \ arg => do
             let (_, expr) = underLams (unArg arg)
             let (PRef _ kn, _) = getFnArgs expr
               | _ => pure Nothing
             log "doc.implementation" 20 $ "Got name \{show @{Raw} kn}"
             let (ns, DN dn nm) = splitNS (kn.fullName)
               | _ => do log "doc.implementation" 10 $ "Invalid name \{show @{Raw} kn}"
                         pure Nothing
             let nm = NS ns nm
             Just (idx, gdef) <- lookupCtxtExactI kn.fullName (gamma defs)
               | _ => do log "doc.implementation" 10 $ "Couldn't find \{show @{Raw} nm}"
                         pure Nothing
             pdef <- displayPats True defs (nm, idx, gdef)
             pure (Just pdef)
           pure (vcat $ intersperse "" pds)
      _ => pure (pretty n <++> reflow "is not an implementation definition")
