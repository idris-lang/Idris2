||| Messages exchanged during the IDE protocol
module Protocol.IDE

import Protocol.SExp
import Data.List

import public Protocol.IDE.Command    as Protocol.IDE
import public Protocol.IDE.Decoration as Protocol.IDE

------------------------------------------------------------------------

-- TODO: decide whether to refactor into separate modules if needed

public export
data Formatting : Type where
  Bold      : Formatting
  Italic    : Formatting
  Underline : Formatting

export
Show Formatting where
  show Bold      = "bold"
  show Italic    = "italic"
  show Underline = "underline"

export
SExpable Formatting where
  toSExp format = SExpList [ SymbolAtom "text-formatting"
                           , SymbolAtom (show format)
                           ]
  where
    {- This definition looks like it repeats `Show`, but `display` is part
       of the IDE protocol, whereas the `Show` instance doesn't have to be.
    -}
    display : Formatting -> String
    display Bold      = "bold"
    display Italic    = "italic"
    display Underline = "underline"

------------------------------------------------------------------------

-- At most one decoration & one formatting
-- (We could use `These` to guarantee non-emptiness but I am not
-- convinced this will stay being just 2 fields e.g. the emacs mode
-- has support for tagging things as errors, adding links, etc.)
public export
record Properties where
  constructor MkProperties
  decor  : Maybe Decoration
  format : Maybe Formatting

export
mkDecor : Decoration -> Properties
mkDecor dec = MkProperties (Just dec) Nothing

export
mkFormat : Formatting -> Properties
mkFormat = MkProperties Nothing . Just

export
SExpable Properties where
  toSExp (MkProperties dec form)  = SExpList $ catMaybes
    [ toSExp <$> form
    , toSExp <$> dec
    ]

------------------------------------------------------------------------
