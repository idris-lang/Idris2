module Parser.Support

import public Libraries.Text.Lexer.Tokenizer
import public Libraries.Text.Lexer
import public Libraries.Text.Parser
import Libraries.Data.String.Extra
import public Libraries.Text.PrettyPrint.Prettyprinter

import Core.TT
import Core.Core
import Data.List
import Parser.Unlit
import public Parser.Support.Escaping

%default total

export
fromLitError : OriginDesc -> LiterateError -> Error
fromLitError origin (MkLitErr l c _) = LitFail (MkFC origin (l, c) (l, c + 1))

export
fromLexError : OriginDesc -> (StopReason, Int, Int, String) -> Error
fromLexError origin (ComposeNotClosing begin end, _, _, _)
    = LexFail (MkFC origin begin end) "Bracket is not properly closed."
fromLexError origin (_, l, c, _)
    = LexFail (MkFC origin (l, c) (l, c + 1)) "Can't recognise token."

export
fromParsingErrors : (Show token, Pretty ann token) =>
                    OriginDesc -> List1 (ParsingError token) -> Error
fromParsingErrors origin = ParseFail . (map fromError)
  where
    fromError : ParsingError token -> (FC, String)
    fromError (Error msg Nothing)
        = (MkFC origin (0, 0) (0, 0), msg +> '.')
    fromError (Error msg (Just t))
        = let start = startBounds t; end = endBounds t in
            let fc = if start == end
                      then MkFC origin start (mapSnd (+1) start)
                      else MkFC origin start end
            in (fc, msg +> '.')

export
getCharLit : String -> Maybe Char
getCharLit str
   = do e <- unescape 0 str
        if length e == 1
           then Just (assert_total (prim__strHead e))
           else if length e == 0 -- parsed the NULL character that terminated the string!
                   then Just '\0000'
                   else Nothing
