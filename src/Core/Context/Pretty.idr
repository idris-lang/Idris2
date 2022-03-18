module Core.Context.Pretty

import Data.String
import Idris.Pretty

import Core.Case.CaseTree
import Core.Context.Context

import Libraries.Data.String.Extra

%default covering

export
Pretty Def where
  pretty None = "undefined"
  pretty (PMDef _ args ct _ pats)
    = vcat [ "Arguments" <++> pretty args
           , "Compile time tree:" <++> pretty ct
           ]
  pretty (DCon tag arity nt)
    = vcat $ "Data constructor:" :: map (indent 2)
        ([ "tag:" <++> pretty tag
         , "arity:" <++> pretty arity
         ] ++ maybe [] (\ n => ["newtype by:" <++> pretty n]) nt)
  pretty (TCon tag arity ps ds u ms cons det)
    = vcat $ "Type constructor:" :: map (indent 2)
        ([ "tag:" <++> pretty tag
         , "arity:" <++> pretty arity
         , "parameter positions:" <++> pretty ps
         , "constructors:" <++> pretty cons
         ] ++ (("mutual with:" <++> pretty ms) <$ guard (not $ null ms))
           ++ (maybe [] (\ pos => ["detaggable by:" <++> pretty pos]) det))
  pretty (ExternDef arity)
    = vcat $ "External definition:" :: map (indent 2)
         [ "arity:" <++> pretty arity ]
  pretty (ForeignDef arity calls)
    = vcat $ "Foreign definition:" :: map (indent 2)
        [ "arity:" <++> pretty arity
        , "bindings:" <++> pretty calls ]
  pretty (Builtin {arity} _)
    = vcat $ "Builtin:" :: map (indent 2)
        [ "arity:" <++> pretty arity ]
  pretty (Hole numlocs hf)
    = vcat $ "Hole:" :: map (indent 2)
        ("Implicitly bound name" <$ guard (implbind hf))
  pretty (BySearch rig depth def)
    = vcat $ "Search:" :: map (indent 2)
        [ "depth:" <++> pretty depth
        , "in:" <++> pretty def ]
  pretty (Guess tm _ cs)
    = vcat $ "Guess:" :: map (indent 2)
        [ "solution:" <++> pretty tm
        , "when:" <++> pretty cs ]
  pretty (UniverseLevel i)
    = "Universe level #" <+> pretty i
  pretty ImpBind = "Bound name"
  pretty Delayed = "Delayed"
