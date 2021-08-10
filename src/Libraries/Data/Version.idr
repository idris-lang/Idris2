||| Provides semantic versioning `Version` type and utilities.
||| See [semver](https://semver.org/) for proper definition of semantic versioning
module Libraries.Data.Version

import Data.List
import Data.String

import Libraries.Text.Parser
import Libraries.Text.Lexer

%default total

||| Semantic versioning with optional tag
public export
record Version where
  constructor MkVersion
  ||| Semantic version
  ||| Should follow the (major, minor, patch) convention
  semVer : (Nat, Nat, Nat)
  ||| Optional tag
  ||| Usually contains git sha1 of this software's build in between releases
  versionTag : Maybe String

||| String representation of a Version with optional display of `tag`
export
showVersion : Bool -> Version -> String
showVersion tag (MkVersion (maj,min,patch) versionTag) =
  concat (intersperse "." (map show [ maj, min, patch])) ++
         if tag then showTag else ""
  where
    showTag : String
    showTag = case versionTag of
                Nothing => ""
                Just tag => "-" ++ tag

export
Show Version where
  show = showVersion True

export
Eq Version where
  (==) (MkVersion ver tag) (MkVersion ver' tag') = ver == ver' && tag == tag'

export
Ord Version where
  compare (MkVersion ver tag) (MkVersion ver' tag')  =
    case compare ver ver' of
      EQ => compare tag tag'
      other => other

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

data VersionTokenKind = VersionText | VersionNum | VersionDot | VersionDash

Eq VersionTokenKind where
  (==) VersionText VersionText = True
  (==) VersionNum VersionNum = True
  (==) VersionDot VersionDot = True
  (==) VersionDash VersionDash = True
  (==) _ _ = False


VersionToken : Type
VersionToken = Token VersionTokenKind

TokenKind VersionTokenKind where
  TokType VersionText = String
  TokType VersionDot = ()
  TokType VersionDash = ()
  TokType VersionNum = Nat

  tokValue VersionText x = x
  tokValue VersionDot _ = ()
  tokValue VersionDash _ = ()
  tokValue VersionNum n = stringToNatOrZ n

versionTokenMap : TokenMap VersionToken
versionTokenMap = toTokenMap $
  [ (is '.', VersionDot)
  , (is '-', VersionDash)
  , (digits, VersionNum)
  , (some alphaNum, VersionText)
  ]

lexVersion : String -> List (WithBounds VersionToken)
lexVersion str =
  let
    (tokens, _, _, _) = lex versionTokenMap str
  in
    tokens


versionParser : Grammar () VersionToken True Version
versionParser = do
  maj <- match VersionNum
  match VersionDot
  min <- match VersionNum
  match VersionDot
  patch <- match VersionNum
  optTag <- optional $ match VersionDash *> match VersionText
  pure $ MkVersion (maj, min, patch) optTag

||| Parse given string into a proper `Version` record
|||
||| Expected format must be:
||| ```
||| <major>.<minor>.<patch>(-<tag>)?
||| ```
||| where <major>, <minor> and <patch> are natural integers and tag is an optional
||| alpha-numeric string.
export
parseVersion : String -> Maybe Version
parseVersion str =
  case parse versionParser (lexVersion str) of
    Right (_, version, []) => Just version
    _ => Nothing
