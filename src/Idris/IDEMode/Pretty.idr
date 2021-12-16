module Idris.IDEMode.Pretty

import Protocol.IDE
import Idris.Pretty
import Idris.Doc.Annotations

------------------------------------------------------------------------
-- Text properties supported by the IDE mode
------------------------------------------------------------------------

export
syntaxToProperties : IdrisSyntax -> Maybe Properties
syntaxToProperties syn = mkDecor <$> syntaxToDecoration syn

export
annToProperties : IdrisAnn -> Maybe Properties
annToProperties Warning       = Just $ MkProperties
                                 { decor = Just Postulate
                                 , format = Just Bold
                                 }
annToProperties Error         = Just $ MkProperties
                                 { decor = Just $ Postulate
                                 , format = Just Bold
                                 }
annToProperties ErrorDesc     = Nothing
annToProperties FileCtxt      = Just $ mkDecor Typ
annToProperties Code          = Just $ mkDecor Bound
annToProperties Meta          = Just $ mkDecor Function
annToProperties (Syntax syn)  = syntaxToProperties syn
annToProperties UserDocString = Just $ mkDecor Comment

export
docToProperties : IdrisDocAnn -> Maybe Properties
docToProperties Header        = pure $ mkFormat Underline
docToProperties Deprecation   = pure $ mkFormat Bold
docToProperties Declarations  = Nothing
docToProperties (Decl _)      = Nothing
docToProperties DocStringBody = Nothing
docToProperties UserDocString = Nothing
docToProperties (Syntax syn)  = syntaxToProperties syn
