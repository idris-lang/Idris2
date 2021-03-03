module Libraries.Control.ANSI.SGR

import Data.List

%default total

public export
data Color
  = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White
  | BrightBlack | BrightRed | BrightGreen | BrightYellow | BrightBlue | BrightMagenta | BrightCyan | BrightWhite

Cast Color String where
  cast Black = "0"
  cast Red = "1"
  cast Green = "2"
  cast Yellow = "3"
  cast Blue = "4"
  cast Magenta = "5"
  cast Cyan = "6"
  cast White = "7"
  cast BrightBlack = "8"
  cast BrightRed = "9"
  cast BrightGreen = "10"
  cast BrightYellow = "11"
  cast BrightBlue = "12"
  cast BrightMagenta = "13"
  cast BrightCyan = "14"
  cast BrightWhite = "15"

public export
data Style
  = Bold | Faint | NotBoldOrFaint | Italic
  | SingleUnderline | DoubleUnderline | NoUnderline
  | Striked | NotStriked

Cast Style String where
  cast Bold = "1"
  cast Faint = "2"
  cast NotBoldOrFaint = "22"
  cast Italic = "3"
  cast SingleUnderline = "4"
  cast DoubleUnderline = "21"
  cast NoUnderline = "24"
  cast Striked = "9"
  cast NotStriked = "29"

public export
data Blink = Slow | Rapid | NoBlink

Cast Blink String where
  cast Slow = "5"
  cast Rapid = "6"
  cast NoBlink = "25"

public export
data SGR
  = Reset
  | SetForeground Color
  | SetBackground Color
  | SetStyle Style
  | SetBlink Blink

||| Returns the ANSI escape code equivalent to the list of operations provided.
export
escapeSGR : List SGR -> String
escapeSGR xs = "\x1B[" ++ concat (intersperse ";" (toCode <$> xs)) ++ "m"
  where
    toCode : SGR -> String
    toCode Reset = "0"
    toCode (SetForeground c) = "38;5;" ++ cast c
    toCode (SetBackground c) = "48;5;" ++ cast c
    toCode (SetStyle s) = cast s
    toCode (SetBlink b) = cast b
