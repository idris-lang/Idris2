module Idris.Pretty.Annotations

import Algebra
import Data.String
import Core.Name
import Libraries.Text.PrettyPrint.Prettyprinter


import Libraries.Data.String.Extra -- otherwise bootstrapping complains

%default total

public export
data IdrisSyntax
  = Hole
  | TCon (Maybe Name) -- these may be primitive types
  | DCon (Maybe Name) -- these may be primitive constructors
  | Fun  Name
  | Bound
  | Keyword
  | Pragma

export
keyword : Doc IdrisSyntax -> Doc IdrisSyntax
keyword = annotate Keyword

export
hole : Doc IdrisSyntax -> Doc IdrisSyntax
hole = annotate Hole

export
let_ : Doc IdrisSyntax
let_ = keyword "let"

export
in_ : Doc IdrisSyntax
in_ = keyword "in"

export
case_ : Doc IdrisSyntax
case_ = keyword "case"

export
of_ : Doc IdrisSyntax
of_ = keyword "of"

export
lcurly : Doc IdrisSyntax
lcurly = keyword "{"

export
semi : Doc IdrisSyntax
semi = keyword ";"

export
equals : Doc IdrisSyntax
equals = keyword "="

export
arrow : Doc IdrisSyntax
arrow = keyword "->"

export
fatArrow : Doc IdrisSyntax
fatArrow = keyword "=>"

export
rcurly : Doc IdrisSyntax
rcurly = keyword "}"

export
do_ : Doc IdrisSyntax
do_ = keyword "do"

export
with_ : Doc IdrisSyntax
with_ = keyword "with"

export
record_ : Doc IdrisSyntax
record_ = keyword "record"

export
impossible_ : Doc IdrisSyntax
impossible_ = keyword "impossible"

export
forall_ : Doc IdrisSyntax
forall_ = keyword "forall"

export
auto_ : Doc IdrisSyntax
auto_ = keyword "auto"

export
default_ : Doc IdrisSyntax
default_ = keyword "default"

export
rewrite_ : Doc IdrisSyntax
rewrite_ = keyword "rewrite"

export
pragma : Doc IdrisSyntax -> Doc IdrisSyntax
pragma = annotate Pragma

export
prettyRig : RigCount -> Doc IdrisSyntax
prettyRig = elimSemi (keyword (pretty0 '0') <+> space)
                     (keyword (pretty0 '1') <+> space)
                     (const emptyDoc)
