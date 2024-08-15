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
%hide Vect.catMaybes
%hide Vect.(++)

%hide Libraries.Data.List.SizeOf.map

%hide Core.Name.prettyOp

%hide CompileExpr.(::)
%hide CompileExpr.Nil
%hide String.(::)
%hide String.Nil
%hide Doc.Nil
%hide Subst.(::)
%hide Subst.Nil
%hide CList.(::)
%hide CList.Nil
%hide Stream.(::)
%hide Symbols.equals
%hide Fin.fromInteger
%hide String.indent
%hide Extra.indent
%hide List1.(++)
%hide SnocList.(++)
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

prettyName : Name -> Doc IdrisSyntax
prettyName = pretty0

mutual

  prettyNamedCExp : NamedCExp -> Doc IdrisSyntax
  prettyNamedCExp = prettyPrecNamedCExp Open

  prettyPrecNamedCExp : Prec -> NamedCExp -> Doc IdrisSyntax
  prettyPrecNamedCExp d (NmLocal _ x) = annotate Bound $ prettyName x
  prettyPrecNamedCExp d (NmRef _ x) = annotate (Fun x) $ prettyName x
  prettyPrecNamedCExp d (NmLam _ x y)
    = parenthesise (d > Open) $ keyword "\\" <+> prettyName x <+> fatArrow <++> prettyNamedCExp y
  prettyPrecNamedCExp d (NmLet _ x y z)
      = parenthesise (d > Open) $
          vcat [ let_ <++> prettyName x <++> equals <++> prettyNamedCExp y <++> in_, prettyNamedCExp z ]
  prettyPrecNamedCExp d (NmApp _ x xs)
      = parenthesise (d > Open) $
          sep (prettyNamedCExp x :: map (prettyPrecNamedCExp App) xs)
  prettyPrecNamedCExp d (NmCon _ x ci tag xs)
      = parenthesise (d > Open) $
          sep (prettyCon x ci tag :: map (prettyPrecNamedCExp App) xs)
  prettyPrecNamedCExp d (NmOp _ op xs)
      = parenthesise (d > Open) $ prettyOp op $ map (prettyPrecNamedCExp App) xs
  prettyPrecNamedCExp d (NmExtPrim _ p xs)
      = parenthesise (d > Open) $
          sep (annotate (Fun p) (pretty0 p) :: map (prettyPrecNamedCExp App) xs)
  prettyPrecNamedCExp d (NmForce _  lr x)
      = parenthesise (d > Open) $
          sep [keyword "Force", byShow lr, prettyPrecNamedCExp App x]
  prettyPrecNamedCExp d (NmDelay _ lr x)
      = parenthesise (d > Open) $
          sep [keyword "Delay", byShow lr, prettyPrecNamedCExp App x]
  prettyPrecNamedCExp d (NmConCase _ sc xs def)
      = parenthesise (d > Open) $
          vcat [ case_ <++> prettyNamedCExp sc <++> of_
               , indent 2 (prettyAlts prettyNamedConAlt xs def)]
  prettyPrecNamedCExp d (NmConstCase _ sc xs def)
      = parenthesise (d > Open) $
          vcat [ case_ <++> prettyNamedCExp sc <++> of_
               , indent 2 (prettyAlts prettyNamedConstAlt xs def)]
  prettyPrecNamedCExp d (NmPrimVal _ x) = pretty x
  prettyPrecNamedCExp d (NmErased _) = "___"
  prettyPrecNamedCExp d (NmCrash _ x)
      = parenthesise (d > Open) $
          sep [annotate Keyword "crash", byShow x]

  prettyNamedConAlt : NamedConAlt -> Doc IdrisSyntax
  prettyNamedConAlt (MkNConAlt x ci tag args exp)
        = sep (prettyCon x ci tag :: map prettyName args ++ [fatArrow <+> softline <+> align (prettyNamedCExp exp) ])

  prettyNamedConstAlt : NamedConstAlt -> Doc IdrisSyntax
  prettyNamedConstAlt (MkNConstAlt x exp)
        = pretty x <++> fatArrow <+> softline <+> align (prettyNamedCExp exp)

  prettyAlts : (alt -> Doc IdrisSyntax) -> List alt -> Maybe NamedCExp -> Doc IdrisSyntax
  prettyAlts pre xs def = vcat
    $ zipWith (\ s, p => s <++> pre p)
              (keyword "{" :: (keyword ";" <$ xs))
              xs
   ++ maybe [] (\ deflt => [keyword "; _" <++> fatArrow <+> softline <+> align (prettyNamedCExp deflt)]) def
   ++ [keyword "}"]

prettyCExp : {args : _} -> CExp args -> Doc IdrisSyntax
prettyCExp = prettyNamedCExp . forget

prettyCDef : CDef -> Doc IdrisDocAnn
prettyCDef (MkFun [<] exp) = reAnnotate Syntax $ prettyCExp exp
prettyCDef (MkFun args exp) = reAnnotate Syntax $
  keyword "\\" <++> concatWith (\ x, y => x <+> keyword "," <++> y) (map prettyName $ toList args)
       <++> fatArrow <++> prettyCExp exp
prettyCDef (MkCon mtag arity nt)
  = vcat $ header (maybe "Type" (const "Data") mtag <++> "Constructor") :: map (indent 2)
         ( maybe [] (\ tag => ["tag:" <++> byShow tag]) mtag ++
         [ "arity:" <++> byShow arity ] ++
           maybe [] (\ n => ["newtype by:" <++> byShow n]) nt)
prettyCDef (MkForeign ccs args ret)
  = vcat $ header "Foreign function" :: map (indent 2)
         [ "bindings:" <++> cast (prettyList ccs)
         , "argument types:" <++> byShow args
         , "return type:" <++> byShow ret
         ]
prettyCDef (MkError exp) = "Error:" <++> reAnnotate Syntax (prettyCExp exp)

export
Pretty IdrisDocAnn CDef where
  pretty = prettyCDef
