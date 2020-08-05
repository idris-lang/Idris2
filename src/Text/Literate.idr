||| A simple module to process 'literate' documents.
|||
||| The module uses a lexer to split the document into code blocks,
||| delineated by user-defined markers, and code lines that are
||| indicated be a line marker. The lexer returns a document stripped
||| of non-code elements but preserving the original document's line
||| count. Column numbering of code lines are not preserved.
|||
||| The underlying tokeniser is greedy.
|||
||| Once it identifies a line marker it reads a prettifying space then
||| consumes until the end of line. Once identifies a starting code
||| block marker, the lexer will consume input until the next
||| identifiable end block is encountered. Any other content is
||| treated as part of the original document.
|||
||| Thus, the input literate files *must* be well-formed w.r.t
||| to code line markers and code blocks.
|||
||| A further restriction is that literate documents cannot contain
||| the markers within the document's main text: This will confuse the
||| lexer.
|||
module Text.Literate

import Text.Lexer

import Data.List
import Data.List.Views
import Data.Strings

%default total

untilEOL : Recognise False
untilEOL = manyUntil newline any

line : String -> Lexer
line s = exact s <+> (newline <|> space <+> untilEOL)

block : String -> String -> Lexer
block s e = surround (exact s <+> untilEOL) (exact e <+> untilEOL) any

notCodeLine : Lexer
notCodeLine = newline
           <|> any <+> untilEOL

data Token = CodeBlock String String String
           | Any String
           | CodeLine String String

Show Token where
  showPrec d (CodeBlock l r x) = showCon d "CodeBlock" $ showArg l ++ showArg r ++ showArg x
  showPrec d (Any x)           = showCon d "Any" $ showArg x
  showPrec d (CodeLine m x)    = showCon d "CodeLine" $ showArg m ++ showArg x

rawTokens : (delims  : List (String, String))
         -> (markers : List String)
         -> TokenMap (Token)
rawTokens delims ls =
          map (\(l,r) => (block l r, CodeBlock (trim l) (trim r))) delims
       ++ map (\m => (line m, CodeLine (trim m))) ls
       ++ [(notCodeLine, Any)]

||| Merge the tokens into a single source file.
reduce : List (TokenData Token) -> List String -> String
reduce [] acc = fastAppend (reverse acc)
reduce (MkToken _ _ _ _ (Any x) :: rest) acc = reduce rest (blank_content::acc)
  where
    -- Preserve the original document's line count.
    blank_content : String
    blank_content = fastAppend (replicate (length (lines x)) "\n")

reduce (MkToken _ _ _ _ (CodeLine m src) :: rest) acc =
    if m == trim src
    then reduce rest ("\n"::acc)
    else reduce rest ((substr (length m + 1) -- remove space to right of marker.
                              (length src)
                              src
                      )::acc)

reduce (MkToken _ _ _ _ (CodeBlock l r src) :: rest) acc with (lines src) -- Strip the deliminators surrounding the block.
  reduce (MkToken _ _ _ _ (CodeBlock l r src) :: rest) acc | [] = reduce rest acc -- 1
  reduce (MkToken _ _ _ _ (CodeBlock l r src) :: rest) acc | (s :: ys) with (snocList ys)
    reduce (MkToken _ _ _ _ (CodeBlock l r src) :: rest) acc | (s :: []) | Empty = reduce rest acc -- 2
    reduce (MkToken _ _ _ _ (CodeBlock l r src) :: rest) acc | (s :: (srcs ++ [f])) | (Snoc f srcs rec) =
        reduce rest ("\n" :: unlines srcs :: acc)

-- [ NOTE ] 1 & 2 shouldn't happen as code blocks are well formed i.e. have two deliminators.


public export
record LiterateError where
  constructor MkLitErr
  line   : Int
  column : Int
  input  : String

||| Description of literate styles.
|||
||| A 'literate' style comprises of
|||
||| + a list of code block deliminators (`deliminators`);
||| + a list of code line markers (`line_markers`); and
||| + a list of known file extensions `file_extensions`.
|||
||| Some example specifications:
|||
||| + Bird Style
|||
|||```
|||MkLitStyle Nil [">"] [".lidr"]
|||```
|||
||| + Literate Haskell (for LaTeX)
|||
|||```
|||MkLitStyle [("\\begin{code}", "\\end{code}"),("\\begin{spec}","\\end{spec}")]
|||           Nil
|||           [".lhs", ".tex"]
|||```
|||
||| + OrgMode
|||
|||```
|||MkLitStyle [("#+BEGIN_SRC idris","#+END_SRC"), ("#+COMMENT idris","#+END_COMMENT")]
|||           ["#+IDRIS:"]
|||           [".org"]
|||```
|||
||| + Common Mark
|||
|||```
|||MkLitStyle [("```idris","```"), ("<!-- idris","--!>")]
|||           Nil
|||           [".md", ".markdown"]
|||```
|||
public export
record LiterateStyle where
  constructor MkLitStyle
  ||| The pairs of start and end tags for code blocks.
  deliminators : List (String, String)

  ||| Line markers that indicate a line contains code.
  line_markers : List String

  ||| Recognised file extensions. Not used by the module, but will be
  ||| of use when connecting to code that reads in the original source
  ||| files.
  file_extensions : List String

||| Given a 'literate specification' extract the code from the
||| literate source file (`litStr`) that follows the presented style.
|||
||| @specification The literate specification to use.
||| @litStr  The literate source file.
|||
||| Returns a `LiterateError` if the literate file contains malformed
||| code blocks or code lines.
|||
export
extractCode : (specification : LiterateStyle)
           -> (litStr        : String)
           -> Either LiterateError String
extractCode (MkLitStyle delims markers exts) str =
      case lex (rawTokens delims markers) str of
        (toks, (_,_,"")) => Right (reduce toks Nil)
        (_, (l,c,i))     => Left (MkLitErr l c i)

||| Synonym for `extractCode`.
export
unlit : (specification : LiterateStyle)
     -> (litStr        : String)
     -> Either LiterateError String
unlit = extractCode

||| Is the provided line marked up using a line marker?
|||
||| If the line is suffixed by any one of the style's set of line
||| markers then return length of literate line marker, and the code stripped from the line
||| marker. Otherwise, return Nothing and the unmarked line.
export
isLiterateLine : (specification : LiterateStyle)
              -> (str : String)
              -> Pair (Maybe String) String
isLiterateLine (MkLitStyle delims markers _) str with (lex (rawTokens delims markers) str)
  isLiterateLine (MkLitStyle delims markers _) str | ([MkToken _ _ _ _ (CodeLine m str')], (_,_, "")) = (Just m, str')
  isLiterateLine (MkLitStyle delims markers _) str | (_, _) = (Nothing, str)

||| Given a 'literate specification' embed the given code using the
||| literate style provided.
|||
||| If the style uses deliminators to denote code blocks use the first
||| pair of deliminators in the style. Otherwise use first linemarker
||| in the style. If there is **no style** return the presented code
||| string unembedded.
|||
|||
||| @specification The literate specification to use.
||| @code  The code to embed,
|||
|||
export
embedCode : (specification : LiterateStyle)
         -> (code : String)
         -> String
embedCode (MkLitStyle ((s,e)::delims) _            _) str = unlines [s,str,e]
embedCode (MkLitStyle Nil             (m::markers) _) str = unwords [m, str]
embedCode (MkLitStyle _               _            _) str = str

||| Synonm for `embedCode`
export
relit : (specification : LiterateStyle)
     -> (code : String)
     -> String
relit = embedCode

-- --------------------------------------------------------------------- [ EOF ]
