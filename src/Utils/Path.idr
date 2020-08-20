module Utils.Path

import Data.List
import Data.Maybe
import Data.Nat
import Data.Strings
import Data.String.Extra

import System.Info

import Text.Token
import Text.Lexer
import Text.Parser
import Text.Quantity

infixr 5 </>
infixr 7 <.>


||| The character that separates directories in the path.
export
dirSeparator : Char
dirSeparator = if isWindows then '\\' else '/'

||| The character that separates multiple paths.
export
pathSeparator : Char
pathSeparator = if isWindows then ';' else ':'

||| Windows' path prefixes of path component.
public export
data Volume
  = 
  ||| Windows' Uniform Naming Convention, e.g., a network sharing
  ||| directory: `\\host\c$\Windows\System32`
  UNC String String |
  ||| The drive, e.g., "C:". The disk character is in upper case
  Disk Char

||| A single body of path component.
public export
data Body
  = 
  ||| Represents "."
  CurDir |
  ||| Represents ".."
  ParentDir |
  ||| Common directory or file
  Normal String

||| A parsed cross-platform file system path.
|||
||| The function `parse` constructs a Path component from String,
||| and the function `show` converts in reverse.
|||
||| Trailing separator is only used for display and is ignored while
||| comparing paths.
public export
record Path where
    constructor MkPath
    ||| Windows' path prefix (only on Windows)
    volume : Maybe Volume
    ||| Whether the path contains a root
    hasRoot : Bool
    ||| Path bodies
    body : List Body
    ||| Whether the path terminates with a separator
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
Show Volume where
  show (UNC server share) = "\\\\" ++ server ++ "\\" ++ share
  show (Disk disk) = singleton disk ++ ":"

||| Display the path in the format on the platform.
export
Show Path where
  show p = let sep = singleton dirSeparator
               volStr = fromMaybe "" (map show p.volume)
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

lexPath : String -> List (WithBounds PathToken)
lexPath str = let (tokens, _, _, _) = lex pathTokenMap str in tokens

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
unc : Grammar PathToken True Volume
unc = do count (exactly 2) $ match $ PTPunct '\\'
         server <- match PTText
         bodySeparator
         share <- match PTText
         Core.pure $ UNC server share

-- Example: \\?\server\share
verbatimUnc : Grammar PathToken True Volume
verbatimUnc = do verbatim
                 server <- match PTText
                 bodySeparator
                 share <- match PTText
                 Core.pure $ UNC server share

-- Example: C:
disk : Grammar PathToken True Volume
disk = do text <- match PTText
          disk <- case unpack text of
                       (disk :: xs) => pure disk
                       [] => fail "Expect Disk"
          match $ PTPunct ':'
          pure $ Disk (toUpper disk)

-- Example: \\?\C:
verbatimDisk : Grammar PathToken True Volume
verbatimDisk = do verbatim
                  d <- disk
                  pure d

parseVolume : Grammar PathToken True Volume
parseVolume = verbatimUnc
          <|> verbatimDisk
          <|> unc
          <|> disk

parseBody : Grammar PathToken True Body
parseBody = do text <- match PTText
               the (Grammar _ False _) $
                   case text of
                        ".." => pure ParentDir
                        "." => pure CurDir
                        s => pure (Normal s)

parsePath : Grammar PathToken False Path
parsePath = do vol <- optional parseVolume
               root <- optional (some bodySeparator)
               body <- sepBy (some bodySeparator) parseBody
               trailSep <- optional (some bodySeparator)
               let body = filter (\case Normal s => ltrim s /= ""
                                        _ => True) body
               let body = case body of
                               [] => []
                               (x::xs) => x :: delete CurDir xs
               pure $ MkPath vol (isJust root) body (isJust trailSep)

||| Parse a String into Path component.
|||
||| Returns the path parsed as much as possible from left to right, the 
||| invalid parts on the right end is ignored.
|||
||| Some kind of invalid path is accepted. Relaxing rules:
|||
||| - Both slash('/') and backslash('\\') are parsed as valid directory
|||   separator, regardless of the platform;
||| - Any characters in path body in allowed, e.g., glob like "/root/*";
||| - Verbatim prefix(`\\?\`) that disables the forward
|||   slash (Windows only) is ignored.
||| - Repeated separators are ignored, so "a/b" and "a//b" both have "a" 
|||   and "b" as bodies.
||| - Occurrences of "." are normalized away, except if they are at the
|||   beginning of the path. For example, "a/./b", "a/b/", "a/b/". and 
|||   "a/b" all have "a" and "b" as bodies, but "./a/b" starts with an 
|||   additional `CurDir` body.
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
-- Utils
--------------------------------------------------------------------------------

isAbsolute' : Path -> Bool
isAbsolute' p = if isWindows
                  then case p.volume of
                            Just (UNC _ _) => True
                            Just (Disk _) => p.hasRoot
                            Nothing => False
                  else p.hasRoot

append' : (left : Path) -> (right : Path) -> Path
append' l r = if isAbsolute' r || isJust r.volume
                 then r
                 else if hasRoot r
                         then record { volume = l.volume } r
                         else record { body = l.body ++ r.body,
                                       hasTrailSep = r.hasTrailSep } l

splitParent' : Path -> Maybe (Path, Path)
splitParent' p 
  = case p.body of
         [] => Nothing
         (x::xs) => let parentPath = record { body = init (x::xs),
                                          hasTrailSep = False } p
                        lastPath = MkPath Nothing False [last (x::xs)] p.hasTrailSep in
                      Just (parentPath, lastPath)

parent' : Path -> Maybe Path
parent' p = map fst (splitParent' p) 

fileName' : Path -> Maybe String
fileName' p = findNormal (reverse p.body)
  where
    findNormal : List Body -> Maybe String
    findNormal ((Normal s)::xs) = Just s
    findNormal (CurDir::xs) = findNormal xs
    findNormal _ = Nothing
    
setFileName' : (name : String) -> Path -> Path
setFileName' name p = if isJust (fileName' p)
                         then append' (fromMaybe emptyPath $ parent' p) (parse name)
                         else append' p (parse name)
    
splitFileName : String -> (String, String)
splitFileName name
    = case break (== '.') $ reverse $ unpack name of
           (_, []) => (name, "")
           (_, ['.']) => (name, "")
           (revExt, (dot :: revStem))
              => ((pack $ reverse revStem), (pack $ reverse revExt))

--------------------------------------------------------------------------------
-- Manipulations
--------------------------------------------------------------------------------

||| Returns true if the path is absolute.
|||
||| - On Unix, a path is absolute if it starts with the root,
|||   so isAbsolute and hasRoot are equivalent.
|||
||| - On Windows, a path is absolute if it has a volume and starts
|||   with the root. e.g., `c:\\windows` is absolute, while `c:temp`
|||   and `\temp` are not. In addition, a path with UNC volume is absolute.
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
||| - If the right path has a root but no volume (e.g., `\windows`), it
|||   replaces everything except for the volume (if any) of left.
||| - If the right path has a volume but no root, it replaces left.
|||
||| ```idris example
||| "/usr" </> "local/etc"
||| ```
export
(</>) : (left : String) -> (right : String) -> String
(</>) l r = show $ append' (parse l) (parse r)

||| Join path elements together.
|||
||| ```idris example
||| joinPath ["/usr", "local/etc"] == "/usr/local/etc"
||| ```
export
joinPath : List String -> String
joinPath xs = foldl (</>) "" xs

||| Returns the parent and child.
|||
||| ```idris example
||| splitParent "/usr/local/etc" == Just ("/usr/local", "etc")
||| ```
export
splitParent : String -> Maybe (String, String)
splitParent p = do (a, b) <- splitParent' (parse p)
                   pure $ (show a, show b)

||| Returns the path without its final component, if there is one.
|||
||| Returns Nothing if the path terminates in a root or volume.
export
parent : String -> Maybe String
parent p = map show $ parent' (parse p)

||| Returns a list of all the parents of the path, longest first,
||| self included.
|||
||| ```idris example
||| parents "/etc/kernel" == ["/etc/kernel", "/etc", "/"]
||| ```
export
parents : String -> List String
parents p = map show $ iterate parent' (parse p)

||| Determines whether base is either one of the parents of full.
|||
||| Trailing separator is ignored.
export
startWith : (base : String) -> (full : String) -> Bool
startWith base full = (parse base) `elem` (iterate parent' (parse full))

||| Returns a path that, when appended onto base, yields full.
|||
||| If base is not a prefix of full (i.e., startWith returns false),
||| returns Nothing.
export
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

||| Returns the final body of the path, if there is one.
|||
||| If the path is a normal file, this is the file name. If it's the
||| path of a directory, this is the directory name.
|||
||| Returns Nothing if the final body is "..".
export
fileName : String -> Maybe String
fileName p = fileName' (parse p)

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

||| Updates the file name of the path.
|||
||| If no file name, this is equivalent to appending the name;
||| Otherwise it is equivalent to appending the name to the parent.
export
setFileName : (name : String) -> String -> String
setFileName name p = show $ setFileName' name (parse p)

||| Append a extension to the path.
|||
||| Returns the path as it is if no file name.
|||
||| If `extension` of the path is Nothing, the extension is added; otherwise
||| it is replaced.
||| 
||| If the ext is empty, the extension is dropped.
export
(<.>) : String -> (ext : String) -> String
(<.>) p ext = let p' = parse p 
                  ext = pack $ dropWhile (== '.') (unpack ext)
                  ext = if ltrim ext == "" then "" else "." ++ ext in
                case fileName' p' of
                     Just name => let (stem, _) = splitFileName name in
                                    show $ setFileName' (stem ++ ext) p'
                     Nothing => p
