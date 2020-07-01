module Control.ANSI

import public Control.ANSI.CSI
import public Control.ANSI.SGR

%default total

public export
record DecoratedString where
  constructor MkDString
  sgr : List SGR
  str : String

export
Show DecoratedString where
  show dstr = escapeSGR dstr.sgr ++ dstr.str ++ escapeSGR [Reset]

export
colored : Color -> String -> DecoratedString
colored c = MkDString [SetForeground c]

export
background : Color -> String -> DecoratedString
background c = MkDString [SetBackground c]

export
bolden : String -> DecoratedString
bolden = MkDString [SetStyle Bold]

export
italicize : String -> DecoratedString
italicize = MkDString [SetStyle Italic]

export
underline : String -> DecoratedString
underline = MkDString [SetStyle SingleUnderline]
