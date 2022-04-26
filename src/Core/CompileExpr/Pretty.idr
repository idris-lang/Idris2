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

%hide Symbols.equals

export
Pretty Void CFType where
  pretty = pretty . show

export
Pretty Void LazyReason where
  pretty = pretty . show


prettyFlag : ConInfo -> Doc ann
prettyFlag DATACON = ""
prettyFlag f = pretty0 (show f)


prettyOp : PrimFn arity -> Vect arity (Doc IdrisSyntax) -> Doc IdrisSyntax
prettyOp (Add ty) [v1,v2] = v1 <++> "+" <++> v2
prettyOp (Sub ty) [v1,v2] = v1 <++> "-" <++> v2
prettyOp (Mul ty) [v1,v2] = v1 <++> "*" <++> v2
prettyOp (Div ty) [v1,v2] = v1 <++> "`div`" <++> v2
prettyOp (Mod ty) [v1,v2] = v1 <++> "`mod`" <++> v2
prettyOp (Neg ty) [v] = "-" <++> v
prettyOp (ShiftL ty) [v1,v2] = "shiftl" <++> v1 <++> v2
prettyOp (ShiftR ty) [v1,v2] = "shiftr" <++> v1 <++> v2
prettyOp (BAnd ty) [v1,v2] = v1 <++> "&&" <++> v2
prettyOp (BOr ty) [v1,v2] = v1 <++> "||" <++> v2
prettyOp (BXOr ty) [v1,v2] = v1 <++> "`xor`" <++> v2
prettyOp (LT ty) [v1,v2] = v1 <++> "<" <++> v2
prettyOp (LTE ty) [v1,v2] = v1 <++> "<=" <++> v2
prettyOp (EQ ty) [v1,v2] = v1 <++> "==" <++> v2
prettyOp (GTE ty) [v1,v2] = v1 <++> ">=" <++> v2
prettyOp (GT ty) [v1,v2] = v1 <++> ">" <++> v2
prettyOp StrLength [v] = "length" <++> v
prettyOp StrHead [v] = "head" <++> v
prettyOp StrTail [v] = "tail" <++> v
prettyOp StrIndex [v1,v2] = v1 <++> "[" <+> v2 <+> "]"
prettyOp StrCons [v1,v2] = v1 <++> "::" <++> v2
prettyOp StrAppend [v1,v2] = v1 <++> "++" <++> v2
prettyOp StrReverse [v] = "reverse" <++> v
prettyOp StrSubstr [v1,v2,v3] = v1 <++> "[" <+> v2 <+> "," <++> v3 <+> "]"
prettyOp DoubleExp [v] = "exp" <++> v
prettyOp DoubleLog [v] = "log" <++> v
prettyOp DoublePow [v1,v2] = v1 <++> "`pow`" <++> v2
prettyOp DoubleSin [v] = "sin" <++> v
prettyOp DoubleCos [v] = "cos" <++> v
prettyOp DoubleTan [v] = "tan" <++> v
prettyOp DoubleASin [v] = "asin" <++> v
prettyOp DoubleACos [v] = "acos" <++> v
prettyOp DoubleATan [v] = "atan" <++> v
prettyOp DoubleSqrt [v] = "sqrt" <++> v
prettyOp DoubleFloor [v] = "floor" <++> v
prettyOp DoubleCeiling [v] = "ceiling" <++> v
prettyOp (Cast x y) [v] = "[" <+> pretty x <++> "->" <++> pretty y <+> "]" <++> v
prettyOp BelieveMe [v1,v2,v3] = "believe_me" <++> v1 <++> v2 <++> v3
prettyOp Crash [v1,v2] = "crash" <++> v1 <++> v2

prettyCon : Name -> ConInfo -> Maybe Int -> Doc IdrisSyntax
prettyCon x ci tag
  = hsep [ annotate (DCon (Just x)) (pretty0 x)
         , braces ("tag =" <++> pretty0 tag)
         , prettyFlag ci
         ]

mutual
  export
  Pretty IdrisSyntax NamedCExp where
    prettyPrec d (NmLocal _ x) = "!" <+> pretty0 x
    prettyPrec d (NmRef _ x) = pretty0 x
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
            sep [keyword "Force", pretty0 lr, prettyPrec App x]
    prettyPrec d (NmDelay _ lr x)
        = parenthesise (d > Open) $
            sep [keyword "Delay", pretty0 lr, prettyPrec App x]
    prettyPrec d (NmConCase _ sc xs def)
        = parenthesise (d > Open) $ vcat [case_ <++> pretty sc <++> of_, indent 2 (prettyAlts xs def)]
    prettyPrec d (NmConstCase _ sc xs def)
        = parenthesise (d > Open) $ vcat [case_ <++> pretty sc <++> of_, indent 2 (prettyAlts xs def)]
    prettyPrec d (NmPrimVal _ x) = pretty x
    prettyPrec d (NmErased _) = "___"
    prettyPrec d (NmCrash _ x)
        = parenthesise (d > Open) $
            sep ["crash", pretty0 x]
  export
  Pretty IdrisSyntax NamedConAlt where
    pretty (MkNConAlt x ci tag args exp)
        = sep (prettyCon x ci tag :: map pretty0 args ++ [fatArrow <+> softline <+> align (pretty exp) ])

  export
  Pretty IdrisSyntax NamedConstAlt where
    pretty (MkNConstAlt x exp)
        = pretty x <++> fatArrow <+> softline <+> align (pretty exp)

  prettyAlts : Pretty IdrisSyntax alt => List alt -> Maybe NamedCExp -> Doc IdrisSyntax
  prettyAlts xs def = vcat
    $ zipWith (\ s, p => s <++> pretty p)
              (keyword "{" :: (keyword ";" <$ xs))
              xs
   ++ maybe [] (\ deflt => [indent 2 (keyword "; _" <++> fatArrow <+> softline <+> align (pretty deflt))]) def
   ++ [keyword "}"]

export
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
           ( maybe [] (\ tag => ["tag:" <++> pretty0 tag]) mtag ++
           [ "arity:" <++> pretty0 arity ] ++
             maybe [] (\ n => ["newtype by:" <++> pretty0 n]) nt)
  pretty (MkForeign ccs args ret)
    = vcat $ header "Foreign function" :: map (indent 2)
           [ "bindings:" <++> pretty0 ccs
           , "argument types:" <++> pretty0 args
           , "return type:" <++> pretty0 ret
           ]
  pretty (MkError exp) = "Error:" <++> prettyBy Syntax exp
