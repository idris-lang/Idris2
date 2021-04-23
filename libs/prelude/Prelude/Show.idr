module Prelude.Show

import Builtin
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num
import Prelude.Types

%default total

----------
-- SHOW --
----------

||| The precedence of an Idris operator or syntactic context.
public export
data Prec = Open | Equal | Dollar | Backtick | User Nat | PrefixMinus | App

||| Gives the constructor index of the Prec as a helper for writing
||| implementations.
public export
precCon : Prec -> Integer
precCon Open        = 0
precCon Equal       = 1
precCon Dollar      = 2
precCon Backtick    = 3
precCon (User n)    = 4
precCon PrefixMinus = 5
precCon App         = 6

export
Eq Prec where
  (==) (User m) (User n) = m == n
  (==) x        y        = precCon x == precCon y

export
Ord Prec where
  compare (User m) (User n) = compare m n
  compare x        y        = compare (precCon x) (precCon y)

||| Things that have a canonical `String` representation.
public export
interface Show ty where
  ||| Convert a value to its `String` representation.
  ||| @ x the value to convert
  show : (x : ty) -> String
  show x = showPrec Open x

  ||| Convert a value to its `String` representation in a certain precedence
  ||| context.
  |||
  ||| A value should produce parentheses around itself if and only if the given
  ||| precedence context is greater than or equal to the precedence of the
  ||| outermost operation represented in the produced `String`.  *This is
  ||| different from Haskell*, which requires it to be strictly greater.  `Open`
  ||| should thus always produce *no* outermost parens, `App` should always
  ||| produce outermost parens except on atomic values and those that provide
  ||| their own bracketing, like `Pair` and `List`.
  ||| @ d the precedence context.
  ||| @ x the value to convert
  showPrec : (d : Prec) -> (x : ty) -> String
  showPrec _ x = show x

||| Surround a `String` with parentheses depending on a condition.
||| @ b whether to add parentheses
export
showParens : (b : Bool) -> String -> String
showParens False s = s
showParens True  s = "(" ++ s ++ ")"

||| A helper for the common case of showing a non-infix constructor with at
||| least one argument, for use with `showArg`.
|||
||| Apply `showCon` to the precedence context, the constructor name, and the
||| args shown with `showArg` and concatenated.  Example:
||| ```
||| data Ann a = MkAnn String a
|||
||| Show a => Show (Ann a) where
|||   showPrec d (MkAnn s x) = showCon d "MkAnn" $ showArg s ++ showArg x
||| ```
export
showCon : (d : Prec) -> (conName : String) -> (shownArgs : String) -> String
showCon d conName shownArgs = showParens (d >= App) (conName ++ shownArgs)

||| A helper for the common case of showing a non-infix constructor with at
||| least one argument, for use with `showCon`.
|||
||| This adds a space to the front so the results can be directly concatenated.
||| See `showCon` for details and an example.
export
showArg : Show a => (x : a) -> String
showArg x = " " ++ showPrec App x

firstCharIs : (Char -> Bool) -> String -> Bool
firstCharIs p "" = False
firstCharIs p str = p (assert_total (prim__strHead str))

primNumShow : (a -> String) -> Prec -> a -> String
primNumShow f d x = let str = f x in showParens (d >= PrefixMinus && firstCharIs (== '-') str) str

export
Show Int where
  showPrec = primNumShow prim__cast_IntString

export
Show Integer where
  showPrec = primNumShow prim__cast_IntegerString

export
Show Bits8 where
  showPrec = primNumShow prim__cast_Bits8String

export
Show Bits16 where
  showPrec = primNumShow prim__cast_Bits16String

export
Show Bits32 where
  showPrec = primNumShow prim__cast_Bits32String

export
Show Bits64 where
  showPrec = primNumShow prim__cast_Bits64String

export
Show Double where
  showPrec = primNumShow prim__cast_DoubleString

protectEsc : (Char -> Bool) -> String -> String -> String
protectEsc p f s = f ++ (if firstCharIs p s then "\\&" else "") ++ s

showLitChar : Char -> String -> String
showLitChar '\a'   = ("\\a" ++)
showLitChar '\b'   = ("\\b" ++)
showLitChar '\f'   = ("\\f" ++)
showLitChar '\n'   = ("\\n" ++)
showLitChar '\r'   = ("\\r" ++)
showLitChar '\t'   = ("\\t" ++)
showLitChar '\v'   = ("\\v" ++)
showLitChar '\SO'  = protectEsc (== 'H') "\\SO"
showLitChar '\DEL' = ("\\DEL" ++)
showLitChar '\\'   = ("\\\\" ++)
showLitChar c
    = case getAt (fromInteger (prim__cast_CharInteger c)) asciiTab of
           Just k => strCons '\\' . (k ++)
           Nothing => if (c > '\DEL')
                         then strCons '\\' . protectEsc isDigit (show (prim__cast_CharInt c))
                         else strCons c
  where
    asciiTab : List String
    asciiTab
        = ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
           "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
           "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
           "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US"]

showLitString : List Char -> String -> String
showLitString []        = id
showLitString ('"'::cs) = ("\\\"" ++) . showLitString cs
showLitString (c  ::cs) = (showLitChar c) . showLitString cs

export
Show Char where
  show '\'' = "'\\''"
  show c    = strCons '\'' (showLitChar c "'")

export
Show String where
  show cs = strCons '"' (showLitString (unpack cs) "\"")

export
Show Nat where
  show n = show (the Integer (natToInteger n))

export
Show Bool where
  show True = "True"
  show False = "False"

export
Show () where
  show () = "()"

export
(Show a, Show b) => Show (a, b) where
  show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

export
(Show a, {y : a} -> Show (p y)) => Show (DPair a p) where
    show (y ** prf) = "(" ++ show y ++ " ** " ++ show prf ++ ")"

export
Show a => Show (List a) where
  show xs = "[" ++ show' "" xs ++ "]"
    where
      show' : String -> List a -> String
      show' acc []        = acc
      show' acc [x]       = acc ++ show x
      show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

export
Show a => Show (Maybe a) where
  showPrec d Nothing  = "Nothing"
  showPrec d (Just x) = showCon d "Just" (showArg x)

export
(Show a, Show b) => Show (Either a b) where
  showPrec d (Left x)  = showCon d "Left" $ showArg x
  showPrec d (Right x) = showCon d "Right" $ showArg x
