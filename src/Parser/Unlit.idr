module Parser.Unlit

import Libraries.Utils.Path
import public Libraries.Text.Literate
import Data.String
import Data.List
import Data.List1
import Data.Maybe

import Libraries.Data.List.Extra as Lib

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
hasLitFileExt : (fname : String) -> Maybe (String, String)
hasLitFileExt fname =
  do let toExtension = concatMap ("." ++)
     -- split the extensions off a file
     -- e.g. "Cool.shared.org.lidr" becomes ("Cool", ["shared", "org", "lidr"])
     let (bn, exts) = splitExtensions fname
     flip choiceMap listOfExtensionsLiterate $ \ candidate =>
       do -- take candidate apart e.g. ".org.lidr" becomes ["org", "lidr"]
          -- we assume the candidate starts with a "." and so the first string
          -- should be empty
          let ("" ::: chunks) = map pack $ split ('.' ==) (unpack candidate)
            | _ => err
          -- check ["org", "lidr"] is a suffix of the files' extensions and get
          -- back (["shared"], ["org", "lidr"])
          (nm, exts) <- Lib.suffixOfBy (\ v, w => v <$ guard (v == w)) chunks exts
          -- return the basename extended with the leftover extensions, paired with the match
          -- e.g. ("Cool.shared", ".org.lidr")
          pure (bn ++ toExtension nm, toExtension exts)

  where

    err : a
    err = assert_total
        $ idris_crash #"Internal error: all literate extensions should start with a ".""#

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
