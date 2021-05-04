module Libraries.Utils.Path

import Data.List
import Data.Maybe
import Data.Nat
import Data.Strings
import Libraries.Data.String.Extra

import Libraries.Text.Token
import Libraries.Text.Lexer
import Libraries.Text.Parser
import Libraries.Text.Quantity

import System.Info

infixr 5 </>, />
infixr 7 <.>


||| The character that separates directories in the path.
export
dirSeparator : Char
dirSeparator = if isWindows then '\\' else '/'

||| The character that separates multiple paths.
export
pathSeparator : Char
pathSeparator = if isWindows then ';' else ':'

||| Windows path prefix.
public export
data Volume
  =
  ||| Windows Uniform Naming Convention, consisting of server name and share
  ||| directory.
  |||
  ||| Example: `\\localhost\share`
  UNC String String |
  ||| The drive.
  |||
  ||| Example: `C:`
  Disk Char

||| A single body in path.
public export
data Body
  =
  ||| Represents ".".
  CurDir |
  ||| Represents "..".
  ParentDir |
  ||| Directory or file.
  Normal String

||| A parsed cross-platform file system path.
|||
||| Use the function `parse` to constructs a Path from String, and use the
||| function `show` to convert in reverse.
|||
||| Trailing separator is only used for display and is ignored when comparing
||| paths.
public export
record Path where
    constructor MkPath
    ||| Windows path prefix (only for Windows).
    volume : Maybe Volume
    ||| Whether the path contains root.
    hasRoot : Bool
    ||| Path bodies.
    body : List Body
    ||| Whether the path terminates with a separator.
    hasTrailSep : Bool

export
Eq Volume where
  (==) (UNC l1 l2) (UNC r1 r2) = l1 == r1 && r1 == r2
  (==) (Disk l) (Disk r) = l == r
  (==) _ _ = False

export
Eq Body where
  (==) CurDir CurDir = True
  (==) ParentDir ParentDir = True
  (==) (Normal l) (Normal r) = l == r
  (==) _ _ = False

export
Eq Path where
  (==) (MkPath l1 l2 l3 _) (MkPath r1 r2 r3 _) =
    l1 == r1 && l2 == r2 && l3 == r3

||| An empty path, which represents "".
public export
emptyPath : Path
emptyPath = MkPath Nothing False [] False

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

export
Show Body where
  show CurDir = "."
  show ParentDir = ".."
  show (Normal normal) = normal

export
Show Volume where
  show (UNC server share) = "\\\\" ++ server ++ "\\" ++ share
  show (Disk disk) = Strings.singleton disk ++ ":"

||| Displays the path in the format of this platform.
export
Show Path where
  show path =
    let
      sep = Strings.singleton dirSeparator
      showVol = maybe "" show path.volume
      showRoot = if path.hasRoot then sep else ""
      showBody = join sep $ map show path.body
      showTrail = if path.hasTrailSep then sep else ""
    in
      showVol ++ showRoot ++ showBody ++ showTrail

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

data PathTokenKind = PTText | PTPunct Char

Eq PathTokenKind where
  (==) PTText PTText = True
  (==) (PTPunct c1) (PTPunct c2) = c1 == c2
  (==) _ _ = False

PathToken : Type
PathToken = Token PathTokenKind

TokenKind PathTokenKind where
  TokType PTText = String
  TokType (PTPunct _) = ()

  tokValue PTText x = x
  tokValue (PTPunct _) _ = ()

pathTokenMap : TokenMap PathToken
pathTokenMap = toTokenMap $
  [ (is '/', PTPunct '/')
  , (is '\\', PTPunct '\\')
  , (is ':', PTPunct ':')
  , (is '?', PTPunct '?')
  , (some $ non $ oneOf "/\\:?", PTText)
  ]

lexPath : String -> List (WithBounds PathToken)
lexPath str = let (tokens, _, _, _) = lex pathTokenMap str in tokens

-- match both '/' and '\\' regardless of the platform.
bodySeparator : Grammar PathToken True ()
bodySeparator = (match $ PTPunct '\\') <|> (match $ PTPunct '/')

-- Windows will automatically translate '/' to '\\'. And the verbatim prefix,
-- i.e., `\\?\`, can be used to disable the translation.
-- However, we just parse it and ignore it.
--
-- Example: \\?\
verbatim : Grammar PathToken True ()
verbatim =
  do
    ignore $ count (exactly 2) $ match $ PTPunct '\\'
    match $ PTPunct '?'
    match $ PTPunct '\\'
    pure ()

-- Example: \\server\share
unc : Grammar PathToken True Volume
unc =
  do
    ignore $ count (exactly 2) $ match $ PTPunct '\\'
    server <- match PTText
    bodySeparator
    share <- match PTText
    pure $ UNC server share

-- Example: \\?\server\share
verbatimUnc : Grammar PathToken True Volume
verbatimUnc =
  do
    verbatim
    server <- match PTText
    bodySeparator
    share <- match PTText
    pure $ UNC server share

-- Example: C:
disk : Grammar PathToken True Volume
disk =
  do
    text <- match PTText
    disk <- case unpack text of
              (disk :: xs) => pure disk
              [] => fail "Expects disk"
    match $ PTPunct ':'
    pure $ Disk (toUpper disk)

-- Example: \\?\C:
verbatimDisk : Grammar PathToken True Volume
verbatimDisk =
  do
    verbatim
    disk <- disk
    pure disk

parseVolume : Grammar PathToken True Volume
parseVolume =
      verbatimUnc
  <|> verbatimDisk
  <|> unc
  <|> disk

parseBody : Grammar PathToken True Body
parseBody =
  do
    text <- match PTText
    the (Grammar _ False _) $
      case text of
        ".." => pure ParentDir
        "." => pure CurDir
        normal => pure (Normal normal)

parsePath : Grammar PathToken False Path
parsePath =
  do
    vol <- optional parseVolume
    root <- optional (some bodySeparator)
    body <- sepBy (some bodySeparator) parseBody
    trailSep <- optional (some bodySeparator)
    let body = filter (\case Normal s => ltrim s /= ""; _ => True) body
    let body = case body of
                [] => []
                (x::xs) => x :: delete CurDir xs
    pure $ MkPath vol (isJust root) body (isJust trailSep)

||| Parses a String into Path.
|||
||| The string is parsed as much as possible from left to right, and the invalid
||| parts on the right is ignored.
|||
||| Some kind of invalid paths are accepted. The relax rules:
|||
||| - Both slash('/') and backslash('\\') are parsed as valid directory separator,
|||   regardless of the platform;
||| - Any characters in the body in allowed, e.g., glob like "/root/*";
||| - Verbatim prefix(`\\?\`) that disables the forward slash is ignored (for
|||   Windows only).
||| - Repeated separators are ignored, therefore, "a/b" and "a//b" both have "a"
|||   and "b" as bodies.
||| - "." in the body are removed, unless they are at the beginning of the path.
|||   For example, "a/./b", "a/b/", "a/b/." and "a/b" will have "a" and "b" as
|||   bodies, and "./a/b" will starts with `CurDir`.
|||
||| ```idris example
||| parse "C:\\Windows/System32"
||| parse "/usr/local/etc/*"
||| ```
export
parse : String -> Path
parse str =
  case parse parsePath (lexPath str) of
    Right (path, _) => path
    _ => emptyPath

--------------------------------------------------------------------------------
-- Utils
--------------------------------------------------------------------------------

isAbsolute' : Path -> Bool
isAbsolute' path =
  if isWindows then
    case path.volume of
      Just (UNC _ _) => True
      Just (Disk _) => path.hasRoot
      Nothing => False
  else
    path.hasRoot

append' : (left : Path) -> (right : Path) -> Path
append' left right =
  if isAbsolute' right || isJust right.volume then
    right
  else if hasRoot right then
    record { volume = left.volume } right
  else
    record { body = left.body ++ right.body, hasTrailSep = right.hasTrailSep } left

splitPath' : Path -> List Path
splitPath' path =
  case splitRoot path of
    (Just root, other) => root :: iterateBody (path.body) (path.hasTrailSep)
    (Nothing, other) => iterateBody (path.body) (path.hasTrailSep)
  where
    splitRoot : Path -> (Maybe Path, Path)
    splitRoot path@(MkPath Nothing False _ _) = (Nothing, path)
    splitRoot (MkPath vol root xs trailSep) =
      (Just $ MkPath vol root [] False, MkPath Nothing False xs trailSep)

    iterateBody : List Body -> (trailSep : Bool) -> List Path
    iterateBody [] _ = []
    iterateBody [x] trailSep = [MkPath Nothing False [x] trailSep]
    iterateBody (x::y::xs) trailSep =
      (MkPath Nothing False [x] False) :: iterateBody (y::xs) trailSep

splitParent' : Path -> Maybe (Path, Path)
splitParent' path =
  case path.body of
    [] => Nothing
    (x::xs) =>
      let
        parent = record { body = init (x::xs), hasTrailSep = False } path
        child = MkPath Nothing False [last (x::xs)] path.hasTrailSep
      in
        Just (parent, child)

parent' : Path -> Maybe Path
parent' = map fst . splitParent'

fileName' : Path -> Maybe String
fileName' path =
  findNormal $ reverse path.body
where
  findNormal : List Body -> Maybe String
  findNormal ((Normal normal)::xs) = Just normal
  findNormal (CurDir::xs) = findNormal xs
  findNormal _ = Nothing

setFileName' : (name : String) -> Path -> Path
setFileName' name path =
  if isJust (fileName' path) then
    append' (fromMaybe emptyPath $ parent' path) (parse name)
  else
    append' path (parse name)

export
splitFileName : String -> (String, String)
splitFileName name =
  case break (== '.') $ reverse $ unpack name of
    (_, []) => (name, "")
    (_, ['.']) => (name, "")
    (revExt, (dot :: revStem)) =>
      ((pack $ reverse revStem), (pack $ reverse revExt))

--------------------------------------------------------------------------------
-- Methods
--------------------------------------------------------------------------------

||| Returns true if the path is absolute.
|||
||| - On Unix, a path is absolute if it starts with the root, so `isAbsolute` and
|||   `hasRoot` are equivalent.
|||
||| - On Windows, a path is absolute if it starts with a disk and has root or
|||   starts with UNC. For example, `c:\\windows` is absolute, while `c:temp`
|||   and `\temp` are not.
export
isAbsolute : String -> Bool
isAbsolute = isAbsolute' . parse

||| Returns true if the path is relative.
export
isRelative : String -> Bool
isRelative = not . isAbsolute

||| Appends the right path to the left path.
|||
||| If the path on the right is absolute, it replaces the left path.
|||
||| On Windows:
|||
||| - If the right path has a root but no volume (e.g., `\windows`), it replaces
|||   everything except for the volume (if any) of left.
||| - If the right path has a volume but no root, it replaces left.
|||
||| ```idris example
||| parse "/usr" /> "local/etc" == "/usr/local/etc"
||| ```
export
(/>) : (left : Path) -> (right : String) -> Path
(/>) left right = append' left (parse right)

||| Appends the right path to the left path.
|||
||| If the path on the right is absolute, it replaces the left path.
|||
||| On Windows:
|||
||| - If the right path has a root but no volume (e.g., `\windows`), it replaces
|||   everything except for the volume (if any) of left.
||| - If the right path has a volume but no root, it replaces left.
|||
||| ```idris example
||| "/usr" </> "local/etc" == "/usr/local/etc"
||| ```
export
(</>) : (left : String) -> (right : String) -> String
(</>) left right = show $ parse left /> right


||| Joins path components into one.
|||
||| ```idris example
||| joinPath ["/usr", "local/etc"] == "/usr/local/etc"
||| ```
export
joinPath : List String -> String
joinPath xs = show $ foldl (/>) (parse "") xs

||| Splits path into components.
|||
||| ```idris example
||| splitPath "/usr/local/etc" == ["/", "usr", "local", "etc"]
||| splitPath "tmp/Foo.idr" == ["tmp", "Foo.idr"]
||| ```
export
splitPath : String -> List String
splitPath = map show . splitPath' . parse

||| Splits the path into parent and child.
|||
||| ```idris example
||| splitParent "/usr/local/etc" == Just ("/usr/local", "etc")
||| ```
export
splitParent : String -> Maybe (String, String)
splitParent path =
  do
    (parent, child) <- splitParent' (parse path)
    pure (show parent, show child)

||| Returns the path without its final component, if there is one.
|||
||| Returns Nothing if the path terminates by a root or volume.
export
parent : String -> Maybe String
parent = map show . parent' . parse

||| Returns the list of all parents of the path, longest first, self included.
|||
||| ```idris example
||| parents "/etc/kernel" == ["/etc/kernel", "/etc", "/"]
||| ```
export
parents : String -> List String
parents = map show . List.iterate parent' . parse

||| Determines whether the base is one of the parents of target.
|||
||| Trailing separator is ignored.
|||
||| ```idris example
||| "/etc" `isBaseOf` "/etc/kernel"
||| ```
export
isBaseOf : (base : String) -> (target : String) -> Bool
isBaseOf base target =
  let
    MkPath baseVol baseRoot baseBody _ = parse base
    MkPath targetVol targetRoot targetBody _ = parse target
  in
       baseVol == targetVol
    && baseRoot == targetRoot
    && (baseBody `isPrefixOf` targetBody)

||| Returns a path that, when appended to base, yields target.
|||
||| Returns Nothing if the base is not a prefix of the target.
export
dropBase : (base : String) -> (target : String) -> Maybe String
dropBase base target =
  do
    let MkPath baseVol baseRoot baseBody _ = parse base
    let MkPath targetVol targetRoot targetBody targetTrialSep = parse target
    if baseVol == targetVol && baseRoot == targetRoot then Just () else Nothing
    body <- dropBody baseBody targetBody
    pure $ show $ MkPath Nothing False body targetTrialSep
  where
    dropBody : (base : List Body) -> (target : List Body) -> Maybe (List Body)
    dropBody [] ys = Just ys
    dropBody xs [] = Nothing
    dropBody (x::xs) (y::ys) = if x == y then dropBody xs ys else Nothing

||| Returns the last body of the path.
|||
||| If the last body is a file, this is the file name;
||| if it's a directory, this is the directory name;
||| if it's ".", it recurses on the previous body;
||| if it's "..", returns Nothing.
export
fileName : String -> Maybe String
fileName  = fileName' . parse

||| Extracts the file name in the path without extension.
|||
||| The stem is:
|||
||| - Nothing, if there is no file name;
||| - The entire file name if there is no embedded ".";
||| - The entire file name if the file name begins with a "." and has no other ".";
||| - Otherwise, the portion of the file name before the last ".".
export
fileStem : String -> Maybe String
fileStem path = pure $ fst $ splitFileName !(fileName path)

||| Extracts the extension of the file name in the path.
|||
||| The extension is:
|||
||| - Nothing, if there is no file name;
||| - Nothing, if there is no embedded ".";
||| - Nothing, if the file name begins with a "." and has no other ".";
||| - Otherwise, the portion of the file name after the last ".".
export
extension : String -> Maybe String
extension path = fileName path >>=
  filter (/= "") . Just . snd . splitFileName
 where
  -- TODO Use Data.Maybe.filter instead when next minor
  -- release comes out.
  filter : forall a. (a -> Bool) -> Maybe a -> Maybe a
  filter f Nothing = Nothing
  filter f (Just x) = toMaybe (f x) x

||| Updates the file name in the path.
|||
||| If there is no file name, it appends the name to the path;
||| otherwise, it appends the name to the parent of the path.
export
setFileName : (name : String) -> String -> String
setFileName name path = show $ setFileName' name (parse path)

||| Appends a extension to the path.
|||
||| If there is no file name, the path will not change;
||| if the path has no extension, the extension will be appended;
||| if the given extension is empty, the extension of the path will be dropped;
||| otherwise, the extension will be replaced.
|||
||| ```idris example
||| "/tmp/Foo" <.> "idr" == "/tmp/Foo.idr"
||| ```
export
(<.>) : String -> (extension : String) -> String
(<.>) path ext =
  let
    path' = parse path
    ext = pack $ dropWhile (\char => char == '.' || isSpace char) (unpack ext)
    ext = if ext == "" then "" else "." ++ ext
  in
    case fileName' path' of
      Just name =>
        let (stem, _) = splitFileName name in
          show $ setFileName' (stem ++ ext) path'
      Nothing => path

||| Drops the extension of the path.
export
dropExtension : String -> String
dropExtension path = path <.> ""
