module Core.Context.Pretty

import Core.Context
import Core.Env

import Data.String
import Idris.Doc.Annotations

import Idris.Syntax
import Idris.Pretty

import Core.Case.CaseTree
import Core.Case.CaseTree.Pretty
import Core.Context.Context

import Libraries.Data.String.Extra

%hide Env.(:<)
%hide Env.Lin
%hide String.(::)
%hide String.Nil
%hide Doc.Nil
%hide Subst.(:<)
%hide Subst.Lin
%hide CList.(::)
%hide CList.Nil
%hide Stream.(::)
%hide Symbols.equals
%hide String.indent
%hide Extra.indent
%hide List1.(++)
-- %hide SnocList.(++)
%hide String.(++)
%hide Pretty.Syntax
%hide List1.forget

%default covering

namespace Raw
  export
  prettyDef : Def -> Doc IdrisDocAnn
  prettyDef None = "undefined"
  prettyDef (PMDef _ args ct _ pats) =
       let ct = prettyTree ct in
       vcat
        [ "Arguments" <++> cast (prettyList $ toList args)
        , header "Compile time tree" <++> reAnnotate Syntax ct
        ]
  prettyDef (DCon tag arity nt) =
      vcat $ header "Data constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
           ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) nt)
  prettyDef (TCon tag arity ps ds u ms cons det) =
        let enum = hsep . punctuate "," in
        vcat $ header "Type constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
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
  prettyDef (Builtin {arity} _) =
        vcat $ header "Builtin" :: map (indent 2)
          [ "arity:" <++> byShow arity ]
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
  prettyDef : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Def -> Core (Doc IdrisDocAnn)
  prettyDef None = pure "undefined"
  prettyDef (PMDef _ args ct _ pats) = do
      ct <- prettyTree (mkEnv emptyFC _) ct
      pure $ vcat
        [ "Arguments" <++> cast (prettyList $ toList args)
        , header "Compile time tree" <++> reAnnotate Syntax ct
        ]
  prettyDef (DCon tag arity nt) = pure $
      vcat $ header "Data constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
           ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) nt)
  prettyDef (TCon tag arity ps ds u ms cons det) = pure $
        let enum = hsep . punctuate "," in
        vcat $ header "Type constructor" :: map (indent 2)
          ([ "tag:" <++> byShow tag
           , "arity:" <++> byShow arity
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
  prettyDef (Builtin {arity} _) = pure $
        vcat $ header "Builtin" :: map (indent 2)
          [ "arity:" <++> byShow arity ]
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
