module Libraries.Text.Lexer.Tokenizer

import Data.List

import Libraries.Text.Lexer.Core
import Libraries.Text.Lexer
import Libraries.Text.PrettyPrint.Prettyprinter

import public Libraries.Control.Delayed
import public Libraries.Text.Bounded

%default total

||| Description of a language's tokenization rule.
export
data Tokenizer : (tokenType : Type) -> Type where
     Match : Lexer -> (String -> tokenType) -> Tokenizer tokenType
     Compose : (begin : Lexer) ->
               (mapBegin : String -> tokenType) ->
               (tagger : String -> tag) ->
               (middle : Inf (tag -> Tokenizer tokenType)) ->
               (end : tag -> Lexer) ->
               (mapEnd : String -> tokenType) ->
               Tokenizer tokenType
     Alt : Tokenizer tokenType -> Lazy (Tokenizer tokenType) -> Tokenizer tokenType

||| Alternative tokenizer rules.
export
(<|>) : Tokenizer t -> Lazy (Tokenizer t) -> Tokenizer t
(<|>) = Alt

||| Match on a recogniser and cast the string to a token.
export
match : Lexer -> (String -> a) -> Tokenizer a
match = Match

||| Compose other tokenizer. Language composition should be quoted between
||| a begin lexer and a end lexer. The begin token can be used to generate
||| the composition tokenizer and the end lexer.
export
compose : (begin : Lexer) ->
          (mapBegin : String -> a) ->
          (tagger : String -> tag) ->
          (middle : Inf (tag -> Tokenizer a)) ->
          (end : tag -> Lexer) ->
          (mapEnd : String -> a) ->
          Tokenizer a
compose = Compose

||| Stop reason why tokenizer can't make more progress.
||| @ ComposeNotClosing carries the span of composition begin token in the
|||                     form of `(startLine, startCol), (endLine, endCol)`.
public export
data StopReason = EndInput | NoRuleApply | ComposeNotClosing (Int, Int) (Int, Int)

export
Show StopReason where
  show EndInput = "EndInput"
  show NoRuleApply = "NoRuleApply"
  show (ComposeNotClosing start end) = "ComposeNotClosing " ++ show start ++ " " ++ show end

export
Pretty StopReason where
  pretty EndInput = pretty "EndInput"
  pretty NoRuleApply = pretty "NoRuleApply"
  pretty (ComposeNotClosing start end) = "ComposeNotClosing" <++> pretty start <++> pretty end

tokenise : Lexer ->
           Tokenizer a ->
           (line, col : Int) -> List (WithBounds a) ->
           List Char ->
           (List (WithBounds a), (StopReason, Int, Int, List Char))
tokenise reject tokenizer line col acc [] = (reverse acc, EndInput, (line, col, []))
tokenise reject tokenizer line col acc str
    = case scan reject [] str of
           Just _ => (reverse acc, (EndInput, line, col, str))
           Nothing => case getFirstMatch tokenizer str of
                           Right (toks, line', col', rest) =>
                               -- assert total because getFirstMatch must consume something
                               assert_total (tokenise reject tokenizer line' col' (toks ++ acc) rest)
                           Left reason => (reverse acc, reason, (line, col, str))
  where
    countNLs : List Char -> Nat
    countNLs str = List.length (filter (== '\n') str)

    getCols : List Char -> Int -> Int
    getCols x c
        = case span (/= '\n') x of
               (incol, []) => c + cast (length incol)
               (incol, _) => cast (length incol)

    -- get the next lexeme using the `Lexer` in argument, its position and the input
    -- Returns the new position, the lexeme parsed and the rest of the input
    -- If parsing the lexer fails, this returns `Nothing`
    getNext : (lexer : Lexer) ->  (line, col : Int) -> (input : List Char) -> Maybe (String, Int, Int, List Char)
    getNext lexer line col str =
      let Just (token, rest) = scan lexer [] str
            | _ => Nothing
          line' = line + cast (countNLs token)
          col' = getCols token col
          tokenStr = fastPack $ reverse token
       in pure (tokenStr, line', col', rest)

    getFirstMatch : Tokenizer a -> List Char ->
                    Either StopReason (List (WithBounds a), Int, Int, List Char)
    getFirstMatch (Match lex fn) str
        = let Just (tok, line', col', rest) = getNext lex line col str
                | _ => Left NoRuleApply
              tok' = MkBounded (fn tok) False (MkBounds line col line' col')
           in Right ([tok'], line', col', rest)
    getFirstMatch (Compose begin mapBegin tagger middleFn endFn mapEnd) str
        = let Just (beginTok', line', col' , rest) = getNext begin line col str
                | Nothing => Left NoRuleApply
              tag = tagger beginTok'
              middle = middleFn tag
              end = endFn tag
              beginTok'' = MkBounded (mapBegin beginTok') False (MkBounds line col line' col')
              (midToks, (reason, line'', col'', rest'')) =
                    assert_total $ tokenise end middle line' col' [] rest
           in case reason of
                   (ComposeNotClosing _ _) => Left reason
                   _ => let Just (endTok', lineEnd, colEnd, restEnd) =
                                getNext end line'' col'' rest''
                              | _ => Left $ ComposeNotClosing (line, col) (line', col')
                            endTok'' = MkBounded (mapEnd endTok') False (MkBounds line'' col'' lineEnd colEnd)
                         in Right ([endTok''] ++ reverse midToks ++ [beginTok''], lineEnd, colEnd, restEnd)
    getFirstMatch (Alt t1 t2) str
        = case getFirstMatch t1 str of
               Right result => Right result
               Left reason@(ComposeNotClosing _ _) => Left reason
               Left _ => getFirstMatch t2 str

export
lexTo : Lexer ->
        Tokenizer a ->
        String ->
        (List (WithBounds a), (StopReason, Int, Int, String))
lexTo reject tokenizer str
    = let (ts, reason, (l, c, str')) =
              tokenise reject tokenizer 0 0 [] (fastUnpack str) in
          (ts, reason, (l, c, fastPack str'))

||| Given a tokenizer and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the string
||| where there are no recognised tokens.
export
lex : Tokenizer a -> String -> (List (WithBounds a), (StopReason, Int, Int, String))
lex tokenizer str = lexTo (pred $ const False) tokenizer str
