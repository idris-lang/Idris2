module System.Path

import Data.List
import Data.Maybe
import Data.Strings
import Data.String.Extra
import System.Info
import Text.Token
import Text.Lexer
import Text.Parser
import Text.Quantity

infixl 7 </>

isWindows : Bool
isWindows = os `elem` ["windows", "mingw32", "cygwin32"]

||| The character that separates directories in the path.
export
dirSeparator : Char
dirSeparator = if isWindows then '\\' else '/'

||| The character that separates multiple paths.
export
pathSeparator : Char
pathSeparator = if isWindows then ';' else ':'

||| Windows' path prefixes.
|||
||| @ UNC Windows' Uniform Naming Convention, e.g., a network sharing
|||   directory: `\\host\c$\Windows\System32`
||| @ Disk the drive, e.g., "C:". The disk character is in upper case
public export
data Volumn = UNC String String
            | Disk Char

||| A single body of path.
|||
||| @ CurDir "."
||| @ ParentDir ".."
||| @ Normal common directory or file
public export
data Body = CurDir
          | ParentDir
          | Normal String

||| A cross-platform file system path.
|||
||| The function `parse` is the most common way to construct a Path
||| from String, and the function `show` converts in reverse.
|||
||| Trailing separator is only used for display and is ignored while
||| comparing paths.
|||
||| @ volumn Windows' path prefix (only on Windows)
||| @ hasRoot whether the path contains a root
||| @ body path bodies
||| @ hasTrailSep whether the path terminates with a separator
public export
record Path where
    constructor MkPath
    volumn : Maybe Volumn
    hasRoot : Bool
    body : List Body
    hasTrailSep : Bool

export
Eq Volumn where
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
  (==) (MkPath l1 l2 l3 _) (MkPath r1 r2 r3 _) = l1 == r1
                                              && l2 == r2
                                              && l3 == r3

||| An empty path that represents "".
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
  show (Normal s) = s

export
Show Volumn where
  show (UNC server share) = "\\\\" ++ server ++ "\\" ++ share
  show (Disk disk) = singleton disk ++ ":"

||| Display the path in the format on the platform.
export
Show Path where
  show p = let sep = singleton dirSeparator
               volStr = fromMaybe "" (map show p.volumn)
               rootStr = if p.hasRoot then sep else ""
               bodyStr = join sep $ map show p.body
               trailStr = if p.hasTrailSep then sep else "" in
             volStr ++ rootStr ++ bodyStr ++ trailStr

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

export
lexPath : String -> List PathToken
lexPath str = let (tokens, _, _, _) = lex pathTokenMap str in 
                map TokenData.tok tokens

-- match both '/' and '\\' regardless of the platform.
bodySeparator : Grammar PathToken True ()
bodySeparator = (match $ PTPunct '\\') <|> (match $ PTPunct '/')

-- Example: \\?\
-- Windows can automatically translate '/' to '\\'. The verbatim prefix,
-- i.e., `\\?\`, disables the translation.
-- Here, we simply parse and then ignore it.
verbatim : Grammar PathToken True ()
verbatim = do count (exactly 2) $ match $ PTPunct '\\'
              match $ PTPunct '?'
              match $ PTPunct '\\'
              pure ()

-- Example: \\server\share
unc : Grammar PathToken True Volumn
unc = do count (exactly 2) $ match $ PTPunct '\\'
         server <- match PTText
         bodySeparator
         share <- match PTText
         pure $ UNC server share

-- Example: \\?\server\share
verbatimUnc : Grammar PathToken True Volumn
verbatimUnc = do verbatim
                 server <- match PTText
                 bodySeparator
                 share <- match PTText
                 pure $ UNC server share

-- Example: C:
disk : Grammar PathToken True Volumn
disk = do text <- match PTText
          disk <- case unpack text of
                       (disk :: xs) => pure disk
                       [] => fail "Expect Disk"
          match $ PTPunct ':'
          pure $ Disk (toUpper disk)

-- Example: \\?\C:
verbatimDisk : Grammar PathToken True Volumn
verbatimDisk = do verbatim
                  d <- disk
                  pure d

parseVolumn : Grammar PathToken True Volumn
parseVolumn = verbatimUnc
          <|> verbatimDisk
          <|> unc
          <|> disk

parseBody : Grammar PathToken True Body
parseBody = do text <- match PTText
               the (Grammar _ False _) $
                   case text of
                        " " => fail "Empty body"
                        ".." => pure ParentDir
                        "." => pure CurDir
                        s => pure (Normal s)

parsePath : Grammar PathToken False Path
parsePath = do vol <- optional parseVolumn
               root <- optional bodySeparator
               body <- sepBy bodySeparator parseBody
               trailSep <- optional bodySeparator
               pure $ MkPath vol (isJust root) body (isJust trailSep)

||| Attempt to parse a String into Path.
|||
||| Returns a error message if the parser fails.
|||
||| The parser is relaxed to accept invalid inputs. Relaxing rules:
|||
||| - Both slash('/') and backslash('\\') are parsed as directory separator,
|||   regardless of the platform;
||| - Invalid characters in path body in allowed, e.g., glob like "/root/*";
||| - Ignoring the verbatim prefix(`\\?\`) that disables the forward
|||   slash (Windows only).
|||
||| ```idris example
||| parse "C:\\Windows/System32"
||| ```
||| ```idris example
||| parse "/usr/local/etc/*"
||| ```
export
parse : String -> Path
parse str = case parse parsePath (lexPath str) of
                 Right (p, _) => p
                 _ => emptyPath

--------------------------------------------------------------------------------
-- Manipulations
--------------------------------------------------------------------------------

isAbsolute' : Path -> Bool
isAbsolute' p = if isWindows
                  then case p.volumn of
                            Just (UNC _ _) => True
                            Just (Disk _) => p.hasRoot
                            Nothing => False
                  else p.hasRoot

||| Returns true if the path is absolute.
|||
||| - On Unix, a path is absolute if it starts with the root,
|||   so isAbsolute and hasRoot are equivalent.
|||
||| - On Windows, a path is absolute if it has a volumn and starts
|||   with the root. e.g., `c:\\windows` is absolute, while `c:temp`
|||   and `\temp` are not. In addition, a path with UNC volumn is absolute.
export
isAbsolute : String -> Bool
isAbsolute p = isAbsolute' (parse p)

||| Returns true if the path is relative, i.e., not absolute.
export
isRelative : String -> Bool
isRelative = not . isAbsolute

||| Appends the right path to the left one.
|||
||| If the path on the right is absolute, it replaces the left path.
|||
||| On Windows:
|||
||| - If the right path has a root but no volumn (e.g., `\windows`), it
|||   replaces everything except for the volumn (if any) of left.
||| - If the right path has a volumn but no root, it replaces left.
|||
||| ```idris example
||| pure $ !(parse "/usr") </> !(parse "local/etc")
||| ```
export
(</>) : (left : String) -> (right : String) -> String
(</>) l r = let l = parse l
                r = parse r in
              show $ if isAbsolute' r || isJust r.volumn
                        then r
                        else if hasRoot r
                                then record { volumn = l.volumn } r
                                else record { body = l.body ++ r.body,
                                              hasTrailSep = r.hasTrailSep } l

parent' : Path -> Maybe Path
parent' p = case p.body of
                [] => Nothing
                (x::xs) => Just $ record { body = init (x::xs),
                                           hasTrailSep = False } p

||| Returns the path without its final component, if there is one.
|||
||| Returns Nothing if the path terminates in a root or volumn.
export
parent : String -> Maybe String
parent p = map show $ parent' (parse p)

||| Returns a list of all parents of the path, longest first,
||| self excluded.
|||
||| For example, the parent of the path, and the parent of the
||| parent of the path, and so on. The list terminates in a
||| root or volumn (if any).
export
parents : String -> List String
parents p = map show $ drop 1 $ iterate parent' (parse p)

||| Determines whether base is either one of the parents of full or
||| is identical to full.
|||
||| Trailing separator is ignored.
export
startWith : (base : String) -> (full : String) -> Bool
startWith base full = (parse base) `elem` (iterate parent' (parse full))

||| Returns a path that, when appended onto base, yields full.
|||
||| If base is not a prefix of full (i.e., startWith returns false),
||| returns Nothing.
stripPrefix : (base : String) -> (full : String) -> Maybe String
stripPrefix base full
    = do let MkPath vol1 root1 body1 _ = parse base
         let MkPath vol2 root2 body2 trialSep = parse full
         if vol1 == vol2 && root1 == root2 then Just () else Nothing
         body <- stripBody body1 body2
         pure $ show $ MkPath Nothing False body trialSep
  where
    stripBody : (base : List Body) -> (full : List Body) -> Maybe (List Body)
    stripBody [] ys = Just ys
    stripBody xs [] = Nothing
    stripBody (x::xs) (y::ys) = if x == y then stripBody xs ys else Nothing

fileName' : Path -> Maybe String
fileName' p = case last' p.body of
                   Just (Normal s) => Just s
                   _ => Nothing

||| Returns the final body of the path, if there is one.
|||
||| If the path is a normal file, this is the file name. If it's the
||| path of a directory, this is the directory name.
|||
||| Returns Nothing if the final body is ".." or "."
export
fileName : String -> Maybe String
fileName p = fileName' (parse p)

splitFileName : String -> (String, String)
splitFileName name
    = case break (== '.') $ reverse $ unpack name of
           (_, []) => (name, "")
           (_, ['.']) => (name, "")
           (revExt, (dot :: revStem))
              => ((pack $ reverse revStem), (pack $ reverse revExt))


||| Extracts the stem (non-extension) portion of the file name of path.
|||
||| The stem is:
|||
||| - Nothing, if there is no file name;
||| - The entire file name if there is no embedded ".";
||| - The entire file name if the file name begins with "." and has
|||   no other "."s within;
||| - Otherwise, the portion of the file name before the final "."
export
fileStem : String -> Maybe String
fileStem p = pure $ fst $ splitFileName !(fileName p)

||| Extracts the extension of the file name of path.
|||
||| The extension is:
|||
||| - Nothing, if there is no file name;
||| - Nothing, if there is no embedded ".";
||| - Nothing, if the file name begins with "." and has no other "."s within;
||| - Otherwise, the portion of the file name after the final "."
export
extension : String -> Maybe String
extension p = pure $ snd $ splitFileName !(fileName p)

setFileName' : (name : String) -> Path -> Path
setFileName' name p = record { body $= updateLastBody name } p
  where
    updateLastBody : String -> List Body -> List Body
    updateLastBody s [] = [Normal s]
    updateLastBody s [Normal _] = [Normal s]
    updateLastBody s [x] = x :: [Normal s]
    updateLastBody s (x::xs) = x :: (updateLastBody s xs)

||| Updates the file name of the path.
|||
||| If no file name, this is equivalent to appending the name;
||| Otherwise it is equivalent to appending the name to the parent.
export
setFileName : (name : String) -> String -> String
setFileName name p = show $ setFileName' name (parse p)

||| Updates the extension of the path.
|||
||| Returns Nothing if no file name.
|||
||| If extension is Nothing, the extension is added; otherwise it is replaced.
export
setExtension : (ext : String) -> String -> String
setExtension ext p = let p' = parse p in
                       case fileName' p' of
                            Just name => let (stem, _) = splitFileName name in
                                           show $ setFileName' (stem ++ "." ++ ext) p'
                            Nothing => p
