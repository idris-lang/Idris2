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
    = vcat [ "Arguments" <++> pretty0 args
           , header "Compile time tree" <++> prettyBy Syntax ct
           ]
  pretty (DCon tag arity nt)
    = vcat $ header "Data constructor" :: map (indent 2)
        ([ "tag:" <++> pretty0 tag
         , "arity:" <++> pretty0 arity
         ] ++ maybe [] (\ n => ["newtype by:" <++> pretty0 n]) nt)
  pretty (TCon tag arity ps ds u ms cons det)
    = let enum = hsep . punctuate "," in
      vcat $ header "Type constructor" :: map (indent 2)
        ([ "tag:" <++> pretty0 tag
         , "arity:" <++> pretty0 arity
         , "parameter positions:" <++> pretty0 ps
         , "constructors:" <++> enum ((\ nm => annotate (Syntax $ DCon (Just nm)) (pretty0 nm)) <$> cons)
         ] ++ (("mutual with:" <++> enum (pretty0 <$> ms)) <$ guard (not $ null ms))
           ++ (maybe [] (\ pos => ["detaggable by:" <++> pretty0 pos]) det))
  pretty (ExternDef arity)
    = vcat $ header "External definition" :: map (indent 2)
         [ "arity:" <++> pretty0 arity ]
  pretty (ForeignDef arity calls)
    = vcat $ header "Foreign definition" :: map (indent 2)
        [ "arity:" <++> pretty0 arity
        , "bindings:" <++> pretty0 calls ]
  pretty (Builtin {arity} _)
    = vcat $ header "Builtin" :: map (indent 2)
        [ "arity:" <++> pretty0 arity ]
  pretty (Hole numlocs hf)
    = vcat $ header "Hole" :: map (indent 2)
        ("Implicitly bound name" <$ guard (implbind hf))
  pretty (BySearch rig depth def)
    = vcat $ header "Search" :: map (indent 2)
        [ "depth:" <++> pretty0 depth
        , "in:" <++> pretty0 def ]
  pretty (Guess tm _ cs)
    = vcat $ header "Guess" :: map (indent 2)
        [ "solution:" <++> pretty0 tm
        , "when:" <++> pretty0 cs ]
  pretty (UniverseLevel i)
    = "Universe level #" <+> pretty0 i
  pretty ImpBind = "Bound name"
  pretty Delayed = "Delayed"
