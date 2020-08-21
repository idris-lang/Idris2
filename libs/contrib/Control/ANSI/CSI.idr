module Control.ANSI.CSI

%default total

||| Moves the cursor n columns up.
||| If the cursor is at the edge of the screen it has no effect.
export
cursorUp : Nat -> String
cursorUp n = "\x1B[" ++ show n ++ "A"

export
cursorUp1 : String
cursorUp1 = cursorUp 1

||| Moves the cursor n columns down.
||| If the cursor is at the edge of the screen it has no effect.
export
cursorDown : Nat -> String
cursorDown n = "\x1B[" ++ show n ++ "B"

export
cursorDown1 : String
cursorDown1 = cursorDown 1

||| Moves the cursor n columns forward.
||| If the cursor is at the edge of the screen it has no effect.
export
cursorForward : Nat -> String
cursorForward n = "\x1B[" ++ show n ++ "C"

export
cursorForward1 : String
cursorForward1 = cursorForward 1

||| Moves the cursor n columns back.
||| If the cursor is at the edge of the screen it has no effect.
export
cursorBack : Nat -> String
cursorBack n = "\x1B[" ++ show n ++ "D"

export
cursorBack1 : String
cursorBack1 = cursorBack 1

||| Moves the cursor at the beginning of n lines down.
||| If the cursor is at the edge of the screen it has no effect.
export
cursorNextLine : Nat -> String
cursorNextLine n = "\x1B[" ++ show n ++ "E"

export
cursorNextLine1 : String
cursorNextLine1 = cursorNextLine 1

||| Moves the cursor at the beginning of n lines up.
||| If the cursor is at the edge of the screen it has no effect.
export
cursorPrevLine : Nat -> String
cursorPrevLine n = "\x1B[" ++ show n ++ "F"

export
cursorPrevLine1 : String
cursorPrevLine1 = cursorPrevLine 1

||| Moves the cursor at an arbitrary line and column.
||| Both lines and columns start at 1.
export
cursorMove : (row : Nat) -> (col : Nat) -> String
cursorMove row col = "\x1B[" ++ show row ++ ";" ++ show col ++ "H"

public export
data EraseDirection = Start | End | All

Cast EraseDirection String where
  cast Start = "1"
  cast End = "0"
  cast All = "2"

||| Clears part of the screen.
export
eraseScreen : EraseDirection -> String
eraseScreen to = "\x1B[" ++ cast to ++ "J"

||| Clears part of the line.
export
eraseLine : EraseDirection -> String
eraseLine to = "\x1B[" ++ cast to ++ "K"

||| Scrolls the whole screen up by n lines.
export
scrollUp : Nat -> String
scrollUp n = "\x1B[" ++ show n ++ "S"

export
scrollUp1 : String
scrollUp1 = scrollUp 1

||| Scrolls the whole screen down by n lines.
export
scrollDown : Nat -> String
scrollDown n = "\x1B[" ++ show n ++ "T"

export
scrollDown1 : String
scrollDown1 = scrollDown 1
