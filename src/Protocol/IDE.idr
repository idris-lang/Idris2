||| Messages exchanged during the IDE protocol
module Protocol.IDE

import Protocol.SExp

import public Libraries.Data.Span

import public Protocol.IDE.Command     as Protocol.IDE
import public Protocol.IDE.Decoration  as Protocol.IDE
import public Protocol.IDE.Formatting  as Protocol.IDE
import public Protocol.IDE.FileContext as Protocol.IDE
import public Protocol.IDE.Holes       as Protocol.IDE
import public Protocol.IDE.Result      as Protocol.IDE
import public Protocol.IDE.Highlight   as Protocol.IDE

%default total
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

export
FromSExpable a => FromSExpable (Span a) where
  fromSExp (SExpList [ start
                     , width
                     , ann
                     ]) = do pure $ MkSpan { start = !(fromSExp start)
                                           , length = !(fromSExp width)
                                           , property  = !(fromSExp ann)}
  fromSExp _ = Nothing

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

-- Again, not the most efficient. Probably better to index by the
-- expected return type in the future
export
FromSExpable ReplyPayload where
  fromSExp (SExpList [SymbolAtom "ok", result])
    = do pure $ OK !(fromSExp result) []
  fromSExp (SExpList [SymbolAtom "ok", result, hl])
    = do pure $ OK !(fromSExp result) !(fromSExp hl)
  fromSExp (SExpList
    [ SymbolAtom "ok"
    , SExpList
      [ SymbolAtom "highlight-source"
      , hls]
    ]) = do pure $ HighlightSource !(fromSExp hls)
  fromSExp (SExpList [SymbolAtom "error", msg])
    = do pure $ Error !(fromSExp msg) []
  fromSExp (SExpList [SymbolAtom "error", msg, hl])
    = do pure $ Error !(fromSExp msg) !(fromSExp hl)
  fromSExp _ = Nothing

public export
data Reply =
    ProtocolVersion Int Int
  | Immediate    ReplyPayload Integer
  | Intermediate ReplyPayload Integer
  | WriteString String Integer
  | SetPrompt   String Integer
  | Warning FileContext String Highlighting Integer

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
FromSExpable Reply where
  fromSExp (SExpList [SymbolAtom "protocol-version", major, minor]) =
     do Just $ ProtocolVersion !(fromSExp major) !(fromSExp minor)
  fromSExp (SExpList [SymbolAtom "return", payload, iden]) =
     do Just $ Immediate !(fromSExp payload) !(fromSExp iden)
  fromSExp (SExpList [SymbolAtom "output", payload, iden]) =
     do Just $ Intermediate !(fromSExp payload) !(fromSExp iden)
  fromSExp (SExpList [SymbolAtom "write-string", str, iden]) =
     do Just $ WriteString !(fromSExp str) !(fromSExp iden)
  fromSExp (SExpList [SymbolAtom "set-prompt", str, iden]) =
     do Just $ SetPrompt !(fromSExp str) !(fromSExp iden)
  fromSExp (SExpList [SymbolAtom "warning"
    , SExpList [filename, SExpList [startLine, startCol]
                      , SExpList [endLine  , endCol  ]
                      , str]
    , iden]) = do
      pure $ Warning (MkFileContext
           { file = !(fromSExp filename)
           , range = MkBounds { startLine = !(fromSExp startLine)
                              , startCol  = !(fromSExp startCol)
                              , endLine   = !(fromSExp endLine)
                              , endCol    = !(fromSExp endCol)}
           })
           !(fromSExp str)
           []
           !(fromSExp iden)
  fromSExp (SExpList [SymbolAtom "warning"
    , SExpList [filename, SExpList [startLine, startCol]
                      , SExpList [endLine  , endCol  ]
                      , str, hl]
    , iden]) = do
      pure $ Warning (MkFileContext
           { file = !(fromSExp filename)
           , range = MkBounds { startLine = !(fromSExp startLine)
                              , startCol  = !(fromSExp startCol)
                              , endLine   = !(fromSExp endLine)
                              , endCol    = !(fromSExp endCol)}
           })
           !(fromSExp str)
           !(fromSExp hl)
           !(fromSExp iden)
  fromSExp _ = Nothing

public export
data Request =
    Cmd IDECommand

export
SExpable Request where
  toSExp (Cmd cmd) = toSExp cmd

export
FromSExpable Request where
  fromSExp cmd = do pure $ Cmd !(fromSExp cmd)
