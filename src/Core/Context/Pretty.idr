module Core.Context.Pretty

import Data.String
import Idris.Doc.Annotations

import Idris.Pretty

import Core.Case.CaseTree
import Core.Context.Context

import Libraries.Data.String.Extra

%hide String.(::)
%hide String.Nil
%hide Doc.Nil
%hide SubstEnv.(::)
%hide SubstEnv.Nil
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

export
Pretty IdrisDocAnn Def where
  pretty None = "undefined"
  pretty (PMDef _ args ct _ pats)
    = vcat [ "Arguments" <++> cast (prettyList args)
           , header "Compile time tree" <++> prettyBy Syntax ct
           ]
  pretty (DCon tag arity nt)
    = vcat $ header "Data constructor" :: map (indent 2)
        ([ "tag:" <++> byShow tag
         , "arity:" <++> byShow arity
         ] ++ maybe [] (\ n => ["newtype by:" <++> byShow n]) nt)
  pretty (TCon tag arity ps ds u ms cons det)
    = let enum = hsep . punctuate "," in
      vcat $ header "Type constructor" :: map (indent 2)
        ([ "tag:" <++> byShow tag
         , "arity:" <++> byShow arity
         , "parameter positions:" <++> byShow ps
         , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty0 nm)) <$> cons)
         ] ++ (("mutual with:" <++> enum (pretty0 <$> ms)) <$ guard (not $ null ms))
           ++ (maybe [] (\ pos => ["detaggable by:" <++> byShow pos]) det))
  pretty (ExternDef arity)
    = vcat $ header "External definition" :: map (indent 2)
         [ "arity:" <++> byShow arity ]
  pretty (ForeignDef arity calls)
    = vcat $ header "Foreign definition" :: map (indent 2)
        [ "arity:" <++> byShow arity
        , "bindings:" <++> byShow calls ]
  pretty (Builtin {arity} _)
    = vcat $ header "Builtin" :: map (indent 2)
        [ "arity:" <++> byShow arity ]
  pretty (Hole numlocs hf)
    = vcat $ header "Hole" :: map (indent 2)
        ("Implicitly bound name" <$ guard (implbind hf))
  pretty (BySearch rig depth def)
    = vcat $ header "Search" :: map (indent 2)
        [ "depth:" <++> byShow depth
        , "in:" <++> pretty0 def ]
  pretty (Guess tm _ cs)
    = vcat $ header "Guess" :: map (indent 2)
        [ "solution:" <++> byShow tm
        , "when:" <++> byShow cs ]
  pretty (UniverseLevel i)
    = "Universe level #" <+> byShow i
  pretty ImpBind = "Bound name"
  pretty Delayed = "Delayed"
