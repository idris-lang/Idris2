module Core.Context.Pretty

import Data.String
import Idris.Doc.Annotations

import Idris.Pretty

import Core.Case.CaseTree
import Core.Context.Context

import Libraries.Data.String.Extra

%default covering

export
Pretty IdrisDocAnn Def where
  pretty None = "undefined"
  pretty (PMDef _ args ct _ pats)
    = vcat [ "Arguments" <++> pretty args
           , header "Compile time tree" <++> prettyBy Syntax ct
           ]
  pretty (DCon tag arity nt)
    = vcat $ header "Data constructor" :: map (indent 2)
        ([ "tag:" <++> pretty tag
         , "arity:" <++> pretty arity
         ] ++ maybe [] (\ n => ["newtype by:" <++> pretty n]) nt)
  pretty (TCon tag arity ps ds u ms cons det)
    = let enum = hsep . punctuate "," in
      vcat $ header "Type constructor" :: map (indent 2)
        ([ "tag:" <++> pretty tag
         , "arity:" <++> pretty arity
         , "parameter positions:" <++> pretty ps
         , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty nm)) <$> cons)
         ] ++ (("mutual with:" <++> enum (pretty <$> ms)) <$ guard (not $ null ms))
           ++ (maybe [] (\ pos => ["detaggable by:" <++> pretty pos]) det))
  pretty (ExternDef arity)
    = vcat $ header "External definition" :: map (indent 2)
         [ "arity:" <++> pretty arity ]
  pretty (ForeignDef arity calls)
    = vcat $ header "Foreign definition" :: map (indent 2)
        [ "arity:" <++> pretty arity
        , "bindings:" <++> pretty calls ]
  pretty (Builtin {arity} _)
    = vcat $ header "Builtin" :: map (indent 2)
        [ "arity:" <++> pretty arity ]
  pretty (Hole numlocs hf)
    = vcat $ header "Hole" :: map (indent 2)
        ("Implicitly bound name" <$ guard (implbind hf))
  pretty (BySearch rig depth def)
    = vcat $ header "Search" :: map (indent 2)
        [ "depth:" <++> pretty depth
        , "in:" <++> pretty def ]
  pretty (Guess tm _ cs)
    = vcat $ header "Guess" :: map (indent 2)
        [ "solution:" <++> pretty tm
        , "when:" <++> pretty cs ]
  pretty (UniverseLevel i)
    = "Universe level #" <+> pretty i
  pretty ImpBind = "Bound name"
  pretty Delayed = "Delayed"
