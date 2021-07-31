module Language.JSON.Tokens

import Language.JSON.String
import Text.Token
import Text.Bounded

%default total

public export
strTrue : String
strTrue = "true"

public export
strFalse : String
strFalse = "false"

public export
data Bracket = Open | Close

public export
Eq Bracket where
  (==) Open Open = True
  (==) Close Close = True
  (==) _ _ = False

public export
data Punctuation
  = Comma
  | Colon
  | Square Bracket
  | Curly Bracket

public export
Eq Punctuation where
  (==) Comma Comma = True
  (==) Colon Colon = True
  (==) (Square b1) (Square b2) = b1 == b2
  (==) (Curly b1) (Curly b2) = b1 == b2
  (==) _ _ = False

public export
data JSONTokenKind
  = JTBoolean
  | JTNumber
  | JTString
  | JTNull
  | JTPunct Punctuation
  | JTIgnore

public export
JSONToken : Type
JSONToken = Token JSONTokenKind

public export
Eq JSONTokenKind where
  (==) JTBoolean JTBoolean = True
  (==) JTNumber JTNumber = True
  (==) JTString JTString = True
  (==) JTNull JTNull = True
  (==) (JTPunct p1) (JTPunct p2) = p1 == p2
  (==) _ _ = False

public export
TokenKind JSONTokenKind where
  TokType JTBoolean = Bool
  TokType JTNumber = Double
  TokType JTString = Maybe String
  TokType JTNull = ()
  TokType (JTPunct _) = ()
  TokType JTIgnore = ()

  tokValue JTBoolean x = x == strTrue
  tokValue JTNumber x = cast x
  tokValue JTString x = stringValue x
  tokValue JTNull _ = ()
  tokValue (JTPunct _) _ = ()
  tokValue JTIgnore _ = ()

export
ignored : WithBounds JSONToken -> Bool
ignored (MkBounded (Tok JTIgnore _) _ _) = True
ignored _ = False
