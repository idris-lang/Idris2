module Idris.Doc.Display

import Core.Case.CaseTree
import Core.Context
import Core.Env

import Idris.IDEMode.Holes

import Idris.Pretty
import Idris.Resugar
import Idris.Syntax

import Libraries.Text.PrettyPrint.Prettyprinter.Util

%default covering

export
displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayType defs (n, i, gdef)
  = maybe (do tm <- resugar [] !(normaliseHoles defs [] (type gdef))
              nm <- aliasName (fullname gdef)
              let ann = showCategory id gdef
              pure (ann (pretty nm) <++> colon <++> prettyTerm tm))
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
       pure (prettyTerm lhstm <++> equals <++> prettyTerm rhstm)

export
displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, Int, GlobalDef) ->
              Core (Doc IdrisSyntax)
displayPats defs (n, idx, gdef)
  = case definition gdef of
      PMDef _ _ _ _ pats =>
        do ty <- displayType defs (n, idx, gdef)
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
           PMDef _ _ ct _ [pat]
               => do pure (pretty !(toFullNames ct)) -- displayClause defs pat
           _ => pure (pretty n <++> reflow "is not an implementation definition")
