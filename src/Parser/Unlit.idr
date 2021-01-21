module Parser.Unlit

import public Libraries.Text.Literate
import Data.Strings

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

export
isLitFile : String -> Maybe LiterateStyle
isLitFile fname =
    case isStyle styleBird of
      Just s => Just s
      Nothing => case isStyle styleOrg of
                     Just s => Just s
                     Nothing => case isStyle styleCMark of
                                     Just s => Just s
                                     Nothing => isStyle styleTeX

  where
   hasSuffix : String -> Bool
   hasSuffix ext = isSuffixOf ext fname

   isStyle : LiterateStyle -> Maybe LiterateStyle
   isStyle style =
     if any hasSuffix (file_extensions style)
      then Just style
      else Nothing

export
isLitLine : String -> (Maybe String, String)
isLitLine str =
  case isLiterateLine styleBird str of
     (Just l, s) => (Just l, s)
     otherwise => case isLiterateLine styleOrg str of
                    (Just l, s) => (Just l, s)
                    otherwise => case isLiterateLine styleCMark str of
                                   (Just l, s) => (Just l, s)
                                   otherwise => case isLiterateLine styleTeX str of
                                                   (Just l, s) => (Just l, s)
                                                   otherwise => (Nothing, str)

export
unlit : Maybe LiterateStyle -> String -> Either LiterateError String
unlit Nothing  str = Right str
unlit (Just s) str = unlit s str

export
relit : Maybe String -> String -> String
relit Nothing     str = str
relit (Just mark) str = unwords [mark, str]
