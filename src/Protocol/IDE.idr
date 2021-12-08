||| Messages exchanged during the IDE protocol
module Protocol.IDE

import Protocol.SExp
import Data.List
import Data.Maybe

import public Libraries.Data.Span

import public Protocol.IDE.Command     as Protocol.IDE
import public Protocol.IDE.Decoration  as Protocol.IDE
import public Protocol.IDE.Formatting  as Protocol.IDE
import public Protocol.IDE.FileContext as Protocol.IDE
import public Protocol.IDE.Holes       as Protocol.IDE
import public Protocol.IDE.Result      as Protocol.IDE
import public Protocol.IDE.Highlight   as Protocol.IDE

------------------------------------------------------------------------

public export
Highlighting : Type
Highlighting = List (Span Properties)

export
SExpable a => SExpable (Span a) where
  toSExp (MkSpan start width ann)
    = SExpList [ IntegerAtom (cast start)
               , IntegerAtom (cast width)
               , toSExp ann
               ]

-- TODO: A REPL Option type, see
-- TODO: A MetaVarLemma record
-- TODO: an IdrisVersion record
------------------------------------------------------------------------

public export
data ReplyPayload =
    OK    Result Highlighting
  | HighlightSource (List SourceHighlight)
  | Error String Highlighting

export
SExpable ReplyPayload where
  toSExp (OK    result hl) = SExpList (SymbolAtom "ok" :: toSExp result :: map toSExp hl)
  toSExp (HighlightSource hls) = SExpList
    [ SymbolAtom "ok"
    , SExpList
      [ SymbolAtom "highlight-source"
      , toSExp hls]
    ]
  toSExp (Error msg    hl) = SExpList (SymbolAtom "error" :: toSExp msg :: map toSExp hl)

public export
data Reply =
    ProtocolVersion Int Int
  | Immediate    ReplyPayload Int
  | Intermediate ReplyPayload Int
  -- TODO:
  -- | WriteString
  -- | SetPrompt
  -- | Warning

public export
data Request =
    Cmd IDECommand

export
SExpable Reply where
  toSExp (ProtocolVersion maj min) =  toSExp (SymbolAtom "protocol-version", maj, min)
  toSExp (   Immediate payload id) = SExpList [SymbolAtom "return",
                                                      toSExp payload, toSExp id]
  toSExp (Intermediate payload id) = SExpList [SymbolAtom "output",
                                                      toSExp payload, toSExp id]

export
SExpable Request where
  toSExp (Cmd cmd) = toSExp cmd
