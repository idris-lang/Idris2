module Compiler.ES.Doc

import Data.List

infixl 8 <++>, <?>

public export
data Doc
  = Nil
  | LineBreak
  | SoftSpace -- this will be ignored in compact printing
  | Comment Doc -- this will be ignored in compact printing
  | Text String
  | Nest Nat Doc
  | Seq Doc Doc

export
Semigroup Doc where
  Nil <+> y = y
  x <+> Nil = x
  x <+> y = Seq x y

export
Monoid Doc where
  neutral = Nil

public export %inline
shown : Show a => a -> Doc
shown a = Text (show a)

export %inline
comment : Doc -> Doc
comment = Comment

export
FromString Doc where
  fromString = Text

export
isMultiline : Doc -> Bool
isMultiline []         = False
isMultiline LineBreak  = True
isMultiline SoftSpace  = False
isMultiline (Text x)   = False
isMultiline (Comment x) = isMultiline x
isMultiline (Nest k x) = isMultiline x
isMultiline (Seq x y)  = isMultiline x || isMultiline y

export
(<++>) : Doc -> Doc -> Doc
a <++> b = a <+> " " <+> b

export
vcat : List Doc -> Doc
vcat = concat . intersperse LineBreak

export
hcat : List Doc -> Doc
hcat = concat

export
hsep : List Doc -> Doc
hsep = concat . intersperse " "

export
block : Doc -> Doc
block b = concat ["{", Nest 1 (LineBreak <+> b), LineBreak, "}"]

export
paren : Doc -> Doc
paren d = "(" <+> d <+> ")"

export
lambdaArrow : Doc
lambdaArrow = SoftSpace <+> "=>" <+> SoftSpace

export
softComma : Doc
softComma = "," <+> SoftSpace

export
softColon : Doc
softColon = ":" <+> SoftSpace

export
softEq : Doc
softEq = SoftSpace <+> "=" <+> SoftSpace

export
compact : Doc -> String
compact = fastConcat . go
  where go : Doc -> List String
        go Nil        = []
        go LineBreak  = []
        go SoftSpace  = []
        go (Comment _) = []
        go (Text x)   = [x]
        go (Nest _ y) = go y
        go (Seq x y)  = go x ++ go y

export
pretty : Doc -> String
pretty = fastConcat . go ""
  where nSpaces : Nat -> String
        nSpaces n = fastPack $ replicate n ' '

        go : (spaces : String) -> Doc -> List String
        go _ Nil        = []
        go s LineBreak  = ["\n",s]
        go _ SoftSpace  = [" "]
        go s (Comment x) = "/* " :: go s x ++ [" */"]
        go _ (Text x)   = [x]
        go s (Nest x y) = go (s ++ nSpaces x) y
        go s (Seq x y)  = go s x ++ go s y
