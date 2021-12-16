module Protocol.IDE.Decoration

import Protocol.SExp

%default total

public export
data Decoration : Type where
  Comment   : Decoration
  Typ       : Decoration
  Function  : Decoration
  Data      : Decoration
  Keyword   : Decoration
  Bound     : Decoration
  Namespace : Decoration
  Postulate : Decoration
  Module    : Decoration

public export
Eq Decoration where
  Comment   == Comment   = True
  Typ       == Typ       = True
  Function  == Function  = True
  Data      == Data      = True
  Keyword   == Keyword   = True
  Bound     == Bound     = True
  Namespace == Namespace = True
  Postulate == Postulate = True
  Module    == Module    = True
  _         == _         = False

public export
Show Decoration where
  show Comment   = "comment"
  show Typ       = "type"
  show Function  = "function"
  show Data      = "data"
  show Keyword   = "keyword"
  show Bound     = "bound"
  show Namespace = "namespace"
  show Postulate = "postulate"
  show Module    = "module"


export
SExpable Decoration where
  toSExp decor = SExpList [ SymbolAtom "decor"
                          , SymbolAtom (show decor)
                          ]
  where
    {- This definition looks like it repeats `Show`, but `display` is part
       of the IDE protocol, whereas the `Show` instance doesn't have to be.
    -}
    display : Decoration -> String
    display Comment   = "comment"
    display Typ       = "type"
    display Function  = "function"
    display Data      = "data"
    display Keyword   = "keyword"
    display Bound     = "bound"
    display Namespace = "namespace"
    display Postulate = "postulate"
    display Module    = "module"

export
FromSExpable Decoration where
  fromSExp (SExpList [SymbolAtom "decor", SymbolAtom decor]) =
    case decor of
      "comment"   => Just Comment
      "type"      => Just Typ
      "function"  => Just Function
      "data"      => Just Data
      "keyword"   => Just Keyword
      "bound"     => Just Bound
      "namespace" => Just Namespace
      "postulate" => Just Postulate
      "module"    => Just Module
      _ => Nothing
  fromSExp _ = Nothing
