module Protocol.IDE.Formatting

import Protocol.SExp
import Protocol.IDE.Decoration

import Data.List

%default total

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


export
FromSExpable Formatting where
  fromSExp (SExpList [ SymbolAtom "text-formatting"
                           , SymbolAtom format
                     ]) =
    case format of
       "bold"      => Just Bold
       "italic"    => Just Italic
       "underline" => Just Underline
       _           => Nothing
  fromSExp _ = Nothing

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

export
FromSExpable Properties where
  fromSExp (SExpList props) =
    case props of
      []  => Just $ MkProperties {decor = Nothing, format = Nothing}
      [prop] => do
        let Nothing = fromSExp prop
          | Just decor => Just $ mkDecor decor
        format <- fromSExp prop
        pure $ mkFormat format
      [prop1, prop2] => -- assume the same order as in toSExp
                        -- not part of the protocol though
        do let format = Just !(fromSExp prop1)
           let decor  = Just !(fromSExp prop2)
           pure $ MkProperties {format, decor}
      _ => Nothing
  fromSExp _ = Nothing
