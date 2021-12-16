module Protocol.IDE.FileContext

import Protocol.SExp

import public Libraries.Text.Bounded

%default total

public export
record FileContext where
  constructor MkFileContext
  file : String
  range : Bounds

export
SExpable FileContext where
  toSExp fc =
    SExpList [ SExpList
               [ SymbolAtom "filename", toSExp fc.file ]
             , SExpList [ SymbolAtom "start"
                        , IntegerAtom (cast fc.range.startLine)
                        , IntegerAtom (cast fc.range.startCol)
                        ]
             , SExpList [ SymbolAtom "end"
                        , IntegerAtom (cast fc.range.endLine)
                        , IntegerAtom (cast fc.range.endCol)
                        ]
             ]

export
FromSExpable FileContext where
  fromSExp (SExpList [ SExpList
               [ SymbolAtom "filename", filenameSExp ]
             , SExpList [ SymbolAtom "start"
                        , IntegerAtom startLine
                        , IntegerAtom startCol
                        ]
             , SExpList [ SymbolAtom "end"
                        , IntegerAtom endLine
                        , IntegerAtom endCol
                        ]
             ]) = do file <- fromSExp filenameSExp
                     pure $ MkFileContext {file, range = MkBounds
                       { startLine = cast startLine
                       , startCol  = cast startCol
                       , endLine   = cast endLine
                       , endCol    = cast endCol
                       }}
  fromSExp _ = Nothing
