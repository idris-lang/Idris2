module Core.Context.Pretty

import Core.Env

import Data.String
import Idris.Doc.Annotations

import Idris.Syntax
import Idris.Pretty
import Idris.Resugar

import Libraries.Data.NatSet

%hide Env.Lin
%hide String.(::)
%hide String.Nil
%hide Doc.Nil
%hide CList.(::)
%hide CList.Nil
%hide Stream.(::)
%hide Symbols.equals
%hide String.indent
%hide List1.(++)
%hide String.(++)
%hide Pretty.Syntax
%hide List1.forget

%default covering

namespace Raw
  export
  prettyTree : {vars : _} -> Term vars -> Doc IdrisSyntax
  prettyAlt : {vars : _} -> CaseAlt vars -> Doc IdrisSyntax
  prettyScope : {vars : _} -> CaseScope vars -> Doc IdrisSyntax

  prettyTree (Case fc ct c sc ty alts)
      = let ann = case ty of
                    Erased _ _ => ""
                    _ => space <+> keyword ":" <++> byShow ty
        in case_ <++> annotate Bound (byShow sc) <+> ann <++> of_
         <+> nest 2 (hardline
         <+> vsep (assert_total (map prettyAlt alts)))
  prettyTree tm = byShow tm

  prettyScope (RHS _ tm) = fatArrow <++> byShow tm
  prettyScope (Arg c x sc) = annotate Bound (pretty0 x) <++> prettyScope sc

  prettyAlt (ConCase _ n tag sc)
      = annotate (DCon (Just n)) (pretty0 n) <++> prettyScope sc
  prettyAlt (DelayCase _ _ arg sc) =
        keyword "Delay" <++> pretty0 arg
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (ConstCase _ c sc) =
        pretty c
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (DefaultCase _ sc) =
        keyword "_"
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))

  export
  prettyDef : Def -> Doc IdrisDocAnn
  prettyDef None = "undefined"
  prettyDef (Function _ ct _ pats) =
       let ct = prettyTree ct in
       header "Compile time tree" <++> reAnnotate Syntax ct
  prettyDef (DCon nt tag arity) =
      vcat $ header "Data constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
           ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) (newTypeArg nt))
  prettyDef (TCon arity ps ds u ms cons det) =
        let enum = hsep . punctuate "," in
        vcat $ header "Type constructor" :: map (indent 2)
          ([ "arity:" <++> byShow arity
           , "parameter positions:" <++> byShow ps
           , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty0 nm)) <$> fromMaybe [] cons)
           ] ++ (("mutual with:" <++> enum (pretty0 <$> ms)) <$ guard (not $ null ms))
             ++ (maybe [] (\ pos => ["detaggable by:" <++> byShow pos]) det))
  prettyDef (ExternDef arity) =
      vcat $ header "External definition" :: map (indent 2)
           [ "arity:" <++> byShow arity ]
  prettyDef (ForeignDef arity calls) =
     vcat $ header "Foreign definition" :: map (indent 2)
          [ "arity:" <++> byShow arity
          , "bindings:" <++> byShow calls ]
  prettyDef (Hole numlocs hf) =
        vcat $ header "Hole" :: map (indent 2)
          ("Implicitly bound name" <$ guard (implbind hf))
  prettyDef (BySearch rig depth def) =
        vcat $ header "Search" :: map (indent 2)
          [ "depth:" <++> byShow depth
          , "in:" <++> pretty0 def ]
  prettyDef (Guess tm _ cs) =
        vcat $ header "Guess" :: map (indent 2)
          [ "solution:" <++> byShow tm
          , "when:" <++> byShow cs ]
  prettyDef (UniverseLevel i) = "Universe level #" <+> byShow i
  prettyDef ImpBind = "Bound name"
  prettyDef Delayed = "Delayed"

namespace Resugared
  export
  prettyTree : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> Term vars -> Core (Doc IdrisSyntax)
  prettyAlt : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> CaseAlt vars -> Core (Doc IdrisSyntax)
  prettyScope : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> CaseScope vars -> Core (Doc IdrisSyntax)

  prettyScope env (RHS _ tm) = do
      tm <- prettyTree env tm
      pure $ fatArrow <++> tm
  prettyScope env (Arg c x sc) = do
      sc <- prettyScope (env :< PVar emptyFC top Explicit (Erased emptyFC Placeholder)) sc
      pure $ annotate Bound (pretty0 x) <++> sc

  prettyAlt env (ConCase _ n tag sc) = do
      sc <- prettyScope env sc
      pure $ annotate (DCon (Just n)) (pretty0 n) <++> sc
  prettyAlt env (DelayCase _ _ arg tm) = do
      tm <- prettyTree (mkEnvOnto emptyFC [_,_] env) tm
      pure $ keyword "Delay" <++> pretty0 arg
        <++> fatArrow
        <+> Union (spaces 1 <+> tm) (nest 2 (hardline <+> tm))
  prettyAlt env (ConstCase _ c tm) = do
      tm <- prettyTree env tm
      pure $ pretty c <++> fatArrow <+>
            Union (spaces 1 <+> tm) (nest 2 (hardline <+> tm))
  prettyAlt env (DefaultCase _ tm) = do
      tm <- prettyTree env tm
      pure $ keyword "_" <++> fatArrow <+>
            Union (spaces 1 <+> tm) (nest 2 (hardline <+> tm))

  prettyTree env (Case fc ct c sc ty alts) = do
      ann <- case ty of
                  Erased _ _ => pure ""
                  _ => do ty <- resugar env ty
                          pure (space <+> keyword ":" <++> pretty ty)
      alts <- assert_total (traverse (prettyAlt env) alts)
      pure $ case_ <++> byShow sc <+> ann <++> of_
         <+> nest 2 (hardline <+> vsep alts)
  prettyTree env tm = pretty <$> resugar env tm

  export
  prettyDef : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Def -> Core (Doc IdrisDocAnn)
  prettyDef None = pure "undefined"
  prettyDef (Function _ ct _ pats) = do
        ct <- prettyTree (mkEnv emptyFC _) ct
        pure $ header "Compile time tree" <++> reAnnotate Syntax ct
  prettyDef (DCon nt tag arity) = pure $
      vcat $ header "Data constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
           ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) (newTypeArg nt))
  prettyDef (TCon arity ps ds u ms cons det) = pure $
        let enum = hsep . punctuate "," in
        vcat $ header "Type constructor" :: map (indent 2)
          ([ "arity:" <++> byShow arity
           , "parameter positions:" <++> byShow ps
           , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty0 nm)) <$> fromMaybe [] cons)
           ] ++ (("mutual with:" <++> enum (pretty0 <$> ms)) <$ guard (not $ null ms))
             ++ (maybe [] (\ pos => ["detaggable by:" <++> byShow pos]) det))
  prettyDef (ExternDef arity) = pure $
      vcat $ header "External definition" :: map (indent 2)
           [ "arity:" <++> byShow arity ]
  prettyDef (ForeignDef arity calls) = pure $
     vcat $ header "Foreign definition" :: map (indent 2)
          [ "arity:" <++> byShow arity
          , "bindings:" <++> byShow calls ]
  prettyDef (Hole numlocs hf) = pure $
        vcat $ header "Hole" :: map (indent 2)
          ("Implicitly bound name" <$ guard (implbind hf))
  prettyDef (BySearch rig depth def) = pure $
        vcat $ header "Search" :: map (indent 2)
          [ "depth:" <++> byShow depth
          , "in:" <++> pretty0 def ]
  prettyDef (Guess tm _ cs) = pure $
        vcat $ header "Guess" :: map (indent 2)
          [ "solution:" <++> byShow tm
          , "when:" <++> byShow cs ]
  prettyDef (UniverseLevel i) = pure $ "Universe level #" <+> byShow i
  prettyDef ImpBind = pure "Bound name"
  prettyDef Delayed = pure "Delayed"
