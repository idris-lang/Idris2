module Parser.Unlit

import Libraries.Utils.Path
import public Libraries.Text.Literate
import Data.String
import Data.List
import Data.List1
import Data.Maybe

%default total

public export
data LiterateModes = Bird | Org | CMark

export
styleBird : LiterateStyle
styleBird = MkLitStyle Nil [">", "<"] [".lidr"]

export
styleOrg : LiterateStyle
styleOrg = MkLitStyle
              [ ("#+BEGIN_SRC idris","#+END_SRC")
              , ("#+begin_src idris","#+end_src")
              , ("#+BEGIN_COMMENT idris","#+END_COMMENT")
              , ("#+begin_comment idris","#+end_comment")]
              ["#+IDRIS:"]
              [".org"]

export
styleCMark : LiterateStyle
styleCMark = MkLitStyle
              [("```idris", "```"), ("~~~idris", "~~~"), ("<!-- idris", "-->")]
              Nil
              [".md", ".markdown"]

export
styleTeX : LiterateStyle
styleTeX = MkLitStyle
              [("\\begin{code}", "\\end{code}"), ("\\begin{hidden}", "\\end{hidden}")]
              Nil
              [".tex", ".ltx"]


||| Return the list of extensions used for literate files.
export
listOfExtensionsLiterate : List String
listOfExtensionsLiterate
  = concatMap file_extensions
              [ styleBird
              , styleOrg
              , styleCMark
              , styleTeX
              ]

||| Are we dealing with a valid literate file name, if so return the base name and used extension.
export
hasLitFileExt : (fname : String)
                     -> Maybe (String, String)
hasLitFileExt fname
      = find listOfExtensionsLiterate

  where
    rp : String -> List Char
    rp = (reverse . unpack)

    pr : List Char -> String
    pr = (pack . reverse)

    find : List String -> Maybe (String, String)
    find Nil
      = Nothing

    find (ext::xs)
      = if (isSuffixOf fname ext)
          then let bname_r = (deleteFirstsBy (==) (rp fname) (rp ext))
               in Just (pr bname_r, ext)
          else find xs

||| Are we dealing with a valid literate file name, if so return the identified style.
export
isLitFile : String -> Maybe LiterateStyle
isLitFile fname
    =   isStyle styleBird
    <|> isStyle styleOrg
    <|> isStyle styleCMark
    <|> isStyle styleTeX

  where
   hasSuffix : String -> Bool
   hasSuffix ext = isSuffixOf ext fname

   isStyle : LiterateStyle -> Maybe LiterateStyle
   isStyle style =
     if any hasSuffix (file_extensions style)
      then Just style
      else Nothing

||| Check if the line is that from a literate style.
export
isLitLine : String -> (Maybe String, String)
isLitLine str
    = fromMaybe (Nothing, str) walk
  where
    try : LiterateStyle -> Maybe (Maybe String, String)
    try style
      = case isLiterateLine style str of
          (Just l, s) => Just (Just l, s)
          _           => Nothing

    walk : Maybe (Maybe String, String)
    walk
      =   try styleBird
      <|> try styleOrg
      <|> try styleCMark
      <|> try styleTeX

export
unlit : Maybe LiterateStyle -> String -> Either LiterateError String
unlit Nothing  str = Right str
unlit (Just s) str = unlit s str

export
relit : Maybe String -> String -> String
relit Nothing     str = str
relit (Just mark) str = unwords [mark, str]
