module Idris.Doc.Annotations

import Core.Metadata
import Core.Name

import Idris.Pretty

%default total

public export
data IdrisDocAnn
  = Header
  | Deprecation
  | Declarations
  | Decl Name
  | DocStringBody
  | UserDocString
  | Syntax IdrisSyntax

export
-- TODO: how can we deal with bold & so on?
docToDecoration : IdrisDocAnn -> Maybe Decoration
docToDecoration (Syntax syn) = syntaxToDecoration syn
docToDecoration _ = Nothing

export
styleAnn : IdrisDocAnn -> AnsiStyle
styleAnn Header        = underline
styleAnn Deprecation   = bold
styleAnn Declarations  = []
styleAnn (Decl {})     = []
styleAnn DocStringBody = []
styleAnn UserDocString = []
styleAnn (Syntax syn)  = syntaxAnn syn

export
tCon : Name -> Doc IdrisDocAnn -> Doc IdrisDocAnn
tCon n = annotate (Syntax $ TCon (Just n))

export
dCon : Name -> Doc IdrisDocAnn -> Doc IdrisDocAnn
dCon n = annotate (Syntax $ DCon (Just n))

export
fun : Name -> Doc IdrisDocAnn -> Doc IdrisDocAnn
fun n = annotate (Syntax $ Fun n)

export
header : Doc IdrisDocAnn -> Doc IdrisDocAnn
header d = annotate Header d <+> colon
