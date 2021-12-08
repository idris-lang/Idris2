module Protocol.IDE.Highlight

import Protocol.SExp

import Protocol.IDE.FileContext
import Protocol.IDE.Decoration

public export
record Highlight where
  constructor MkHighlight
  location : FileContext
  name : String
  isImplicit : Bool
  key : String
  decor : Decoration
  docOverview : String
  typ : String
  ns : String

public export
record LwHighlight where
  constructor MkLwHighlight
  location : FileContext
  decor : Decoration

export
SExpable Highlight where
  toSExp (MkHighlight fc nam impl k dec doc t ns)
    = SExpList [ toSExp fc
               , SExpList [ SExpList [ SymbolAtom "name", StringAtom nam ]
                          , SExpList [ SymbolAtom "namespace", StringAtom ns ]
                          , toSExp dec
                          , SExpList [ SymbolAtom "implicit", toSExp impl ]
                          , SExpList [ SymbolAtom "key", StringAtom k ]
                          , SExpList [ SymbolAtom "doc-overview", StringAtom doc ]
                          , SExpList [ SymbolAtom "type", StringAtom t ]
                          ]
               ]

export
SExpable LwHighlight where
  toSExp lwhl = SExpList
                 [ toSExp lwhl.location
                 , SExpList [ toSExp lwhl.decor]
                 ]

public export
data SourceHighlight =
    Full Highlight
  | Lw LwHighlight

export
SExpable SourceHighlight where
  toSExp (Full hl) = toSExp hl
  toSExp (Lw   hl) = toSExp hl
