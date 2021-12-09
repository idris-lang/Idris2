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
  toSExp (OK    result hl) = SExpList (SymbolAtom "ok" :: toSExp result ::
    case hl of
      [] => []
      _ => [SExpList (map toSExp hl)])
  toSExp (HighlightSource hls) = SExpList
    [ SymbolAtom "ok"
    , SExpList
      [ SymbolAtom "highlight-source"
      , toSExp hls]
    ]
  toSExp (Error msg    hl) = SExpList (SymbolAtom "error" :: toSExp msg ::
    case hl of
      [] => []
      _  => [SExpList (map toSExp hl)])

public export
data Reply =
    ProtocolVersion Int Int
  | Immediate    ReplyPayload Integer
  | Intermediate ReplyPayload Integer
  | WriteString String Integer
  | SetPrompt   String Integer
  | Warning FileContext String Highlighting Integer

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
  toSExp (WriteString str id) = SExpList [SymbolAtom "write-string", toSExp str, toSExp id]
  toSExp (SetPrompt str   id) = SExpList [SymbolAtom "set-prompt"  , toSExp str, toSExp id]
  toSExp (Warning fc str spans id) = SExpList [SymbolAtom "warning",
    SExpList $ toSExp fc.file :: toSExp (fc.range.startLine, fc.range.startCol)
                              :: toSExp (fc.range.endLine  , fc.range.endCol  )
                              :: toSExp str :: case spans of
      [] => []
      _  => [SExpList (map toSExp spans)]
      , toSExp id]
export
SExpable Request where
  toSExp (Cmd cmd) = toSExp cmd
