module Core.CompileExpr.Pretty

import Core.Name
import Core.CompileExpr
import Core.TT
import Data.List
import Data.String
import Data.Vect
import Idris.Pretty
import Libraries.Data.String.Extra

%default covering

export
Pretty CFType where
  pretty = pretty . show

export
Pretty LazyReason where
  pretty = pretty . show


prettyFlag : ConInfo -> Doc ann
prettyFlag DATACON = ""
prettyFlag f = " [" <+> pretty (show f) <+> "]"

mutual
  export
  Pretty NamedCExp where
    prettyPrec d (NmLocal _ x) = "!" <+> pretty x
    prettyPrec d (NmRef _ x) = pretty x
    prettyPrec d (NmLam _ x y)
      = parenthesise (d > Open) $ "\\" <+> pretty x <+> "=>" <++> pretty y
    prettyPrec d (NmLet _ x y z) = vcat [ "let" <++> pretty x <++> "=" <++> pretty y <++> "in"
                                  , pretty z
                                  ]
    prettyPrec d (NmApp _ x xs)
        = parenthesise (d > Open) $
            sep (pretty x :: map (prettyPrec App) xs)
    prettyPrec d (NmCon _ x ci tag xs)
        = parenthesise (d > Open) $
            sep (pretty x <+> braces ("tag =" <++> pretty tag) <+> prettyFlag ci
                 :: map (prettyPrec App) xs)
    prettyPrec d (NmOp _ op xs)
        = parenthesise (d > Open) $ prettyOp op $ map (prettyPrec App) xs

      where

        prettyOp : PrimFn arity -> Vect arity (Doc ann) -> Doc ann
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

    prettyPrec d (NmExtPrim _ p xs)
        = parenthesise (d > Open) $
            sep (pretty p :: map (prettyPrec App) xs)
    prettyPrec d (NmForce _  lr x)
        = parenthesise (d > Open) $
            sep ["Force", prettyPrec App lr, prettyPrec App x]
    prettyPrec d (NmDelay _ lr x)
        = parenthesise (d > Open) $
            sep ["Delay", prettyPrec App lr, prettyPrec App x]
    prettyPrec d (NmConCase _ sc xs def)
        = parenthesise (d > Open) $ vcat
            (("case" <++> pretty sc <++> "of")
            :: zipWith (\ s, p => indent 2 $ s <++> pretty p)
                       ("{" :: (";" <$ xs))
                       xs
            ++ maybe [] (\ deflt => [indent 2 ("; _ =>" <+> softline <+> align (pretty deflt))]) def
            ++ [indent 2 "}"])
    prettyPrec d (NmConstCase _ sc xs def)
        = parenthesise (d > Open) $ vcat
            (("case" <++> pretty sc <++> "of")
            :: zipWith (\ s, p => indent 2 $ s <++> pretty p)
                       ("{" :: (";" <$ xs))
                       xs
            ++ maybe [] (\ deflt => [indent 2 ("; _ =>" <+> softline <+> align (pretty deflt))]) def
            ++ [indent 2 "}"])
    prettyPrec d (NmPrimVal _ x) = pretty x
    prettyPrec d (NmErased _) = "___"
    prettyPrec d (NmCrash _ x)
        = parenthesise (d > Open) $
            sep ["crash", prettyPrec App x]
  export
  Pretty NamedConAlt where
    pretty (MkNConAlt x ci tag args exp)
        = sep (pretty x <+> braces ("tag =" <++> pretty tag) <+> prettyFlag ci
               :: map (prettyPrec App) args
               ++ ["=>" <+> softline <+> align (pretty exp) ])

  export
  Pretty NamedConstAlt where
    pretty (MkNConstAlt x exp)
        = pretty x <++> "=>" <+> softline <+> align (pretty exp)

export
{args : _} -> Pretty (CExp args) where
  pretty = pretty . forget


export
Pretty CDef where
  pretty (MkFun [] exp) = pretty exp
  pretty (MkFun args exp) =
    "\\" <++> concatWith (\ x, y => x <+> "," <++> y) (map pretty args)
         <++> "=>" <++> pretty exp
  pretty (MkCon mtag arity nt)
    = vcat $ (maybe "Data" (const "Type") mtag <++> "Constructor:") :: map (indent 2)
           ( maybe [] (\ tag => ["tag:" <++> pretty tag]) mtag ++
           [ "arity:" <++> pretty arity ] ++
             maybe [] (\ n => ["newtype by:" <++> pretty n]) nt)
  pretty (MkForeign ccs args ret)
    = vcat $ "Foreign function:" :: map (indent 2)
           [ "bindings:" <++> pretty ccs
           , "argument types:" <++> pretty args
           , "return type:" <++> pretty ret
           ]
  pretty (MkError exp) = "Error:" <++> pretty exp
