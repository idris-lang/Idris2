module Core.CompileExpr.Pretty

import Core.Name
import Core.CompileExpr
import Core.TT
import Data.List
import Data.String
import Data.Vect
import Idris.Pretty
import Idris.Doc.Annotations
import Libraries.Data.String.Extra

%default covering

%hide Vect.(::)
%hide Vect.Nil
%hide CompileExpr.(::)
%hide CompileExpr.Nil
%hide String.(::)
%hide String.Nil
%hide Doc.Nil
%hide SubstEnv.(::)
%hide SubstEnv.Nil
%hide SubstCEnv.(::)
%hide SubstCEnv.Nil
%hide CList.(::)
%hide CList.Nil
%hide Stream.(::)
%hide Symbols.equals
%hide Fin.fromInteger
%hide String.indent
%hide Extra.indent
%hide List1.(++)
%hide Vect.(++)
-- %hide SnocList.(++)
%hide String.(++)
%hide Pretty.Syntax
%hide List1.forget

prettyFlag : ConInfo -> Maybe (Doc ann)
prettyFlag DATACON = Nothing
prettyFlag f = Just (byShow f)

prettyCon : Name -> ConInfo -> Maybe Int -> Doc IdrisSyntax
prettyCon x ci mtag
  = hsep $ catMaybes
      [ Just (annotate ((if ci == TYCON then TCon else DCon) (Just x)) (pretty0 x))
      , (braces . ("tag =" <++>) . byShow) <$> mtag
      , prettyFlag ci
      ]

mutual
  Pretty IdrisSyntax NamedCExp where
    prettyPrec d (NmLocal _ x) = annotate Bound $ pretty0 x
    prettyPrec d (NmRef _ x) = annotate (Fun x) $ pretty0 x
    prettyPrec d (NmLam _ x y)
      = parenthesise (d > Open) $ keyword "\\" <+> pretty0 x <+> fatArrow <++> pretty y
    prettyPrec d (NmLet _ x y z)
        = parenthesise (d > Open) $
            vcat [ let_ <++> pretty0 x <++> equals <++> pretty y <++> in_, pretty z ]
    prettyPrec d (NmApp _ x xs)
        = parenthesise (d > Open) $
            sep (pretty x :: map (prettyPrec App) xs)
    prettyPrec d (NmCon _ x ci tag xs)
        = parenthesise (d > Open) $
            sep (prettyCon x ci tag :: map (prettyPrec App) xs)
    prettyPrec d (NmOp _ op xs)
        = parenthesise (d > Open) $ prettyOp op $ map (prettyPrec App) xs
    prettyPrec d (NmExtPrim _ p xs)
        = parenthesise (d > Open) $
            sep (annotate (Fun p) (pretty0 p) :: map (prettyPrec App) xs)
    prettyPrec d (NmForce _  lr x)
        = parenthesise (d > Open) $
            sep [keyword "Force", byShow lr, prettyPrec App x]
    prettyPrec d (NmDelay _ lr x)
        = parenthesise (d > Open) $
            sep [keyword "Delay", byShow lr, prettyPrec App x]
    prettyPrec d (NmConCase _ sc xs def)
        = parenthesise (d > Open) $ vcat [case_ <++> pretty sc <++> of_, indent 2 (prettyAlts xs def)]
    prettyPrec d (NmConstCase _ sc xs def)
        = parenthesise (d > Open) $ vcat [case_ <++> pretty sc <++> of_, indent 2 (prettyAlts xs def)]
    prettyPrec d (NmPrimVal _ x) = pretty x
    prettyPrec d (NmErased _) = "___"
    prettyPrec d (NmCrash _ x)
        = parenthesise (d > Open) $
            sep [annotate Keyword "crash", byShow x]

  Pretty IdrisSyntax NamedConAlt where
    pretty (MkNConAlt x ci tag args exp)
        = sep (prettyCon x ci tag :: map pretty0 args ++ [fatArrow <+> softline <+> align (pretty exp) ])

  Pretty IdrisSyntax NamedConstAlt where
    pretty (MkNConstAlt x exp)
        = pretty x <++> fatArrow <+> softline <+> align (pretty exp)

  prettyAlts : Pretty IdrisSyntax alt => List alt -> Maybe NamedCExp -> Doc IdrisSyntax
  prettyAlts xs def = vcat
    $ zipWith (\ s, p => s <++> pretty p)
              (keyword "{" :: (keyword ";" <$ xs))
              xs
   ++ maybe [] (\ deflt => [keyword "; _" <++> fatArrow <+> softline <+> align (pretty deflt)]) def
   ++ [keyword "}"]

{args : _} -> Pretty IdrisSyntax (CExp args) where
  pretty = pretty . forget

export
Pretty IdrisDocAnn CDef where
  pretty (MkFun [] exp) = prettyBy Syntax exp
  pretty (MkFun args exp) = reAnnotate Syntax $
    keyword "\\" <++> concatWith (\ x, y => x <+> keyword "," <++> y) (map pretty0 args)
         <++> fatArrow <++> pretty exp
  pretty (MkCon mtag arity nt)
    = vcat $ header (maybe "Data" (const "Type") mtag <++> "Constructor") :: map (indent 2)
           ( maybe [] (\ tag => ["tag:" <++> byShow tag]) mtag ++
           [ "arity:" <++> byShow arity ] ++
             maybe [] (\ n => ["newtype by:" <++> byShow n]) nt)
  pretty (MkForeign ccs args ret)
    = vcat $ header "Foreign function" :: map (indent 2)
           [ "bindings:" <++> cast (prettyList ccs)
           , "argument types:" <++> byShow args
           , "return type:" <++> byShow ret
           ]
  pretty (MkError exp) = "Error:" <++> prettyBy Syntax exp
