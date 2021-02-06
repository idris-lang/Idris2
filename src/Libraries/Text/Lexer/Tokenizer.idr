module Libraries.Text.Lexer.Tokenizer

import public Libraries.Control.Delayed
import public Libraries.Text.Bounded
import Libraries.Data.Bool.Extra
import Libraries.Data.String.Extra
import Libraries.Text.Lexer.Core
import Libraries.Text.Lexer
import Data.List
import Data.Either
import Data.Nat
import Data.Strings

%default total

||| Description a language's tokenizer rule.
export
data Tokenizer : (tokenType : Type) -> Type where
     Match : Lexer -> (String -> tokenType) -> Tokenizer tokenType
     Compose : (begin : Lexer) ->
               (tagger : String -> tag) ->
               (middle : tag -> Tokenizer midTokenType) ->
               (end : tag -> Lexer) ->
               (map : tag -> List (WithBounds midTokenType) -> tokenType) ->
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

||| Compose other language's tokenizer. Language composition should be
||| quoted between a begin recogniser and a end recogniser. The begin token
||| can be used to generate the composition tokenizer and the end recogniser.
export
compose : (begin : Lexer) ->
          (tagger : String -> tag) ->
          (middle : tag -> Tokenizer b) ->
          (end : tag -> Lexer) ->
          (map : tag -> List (WithBounds b) -> a) ->
          Tokenizer a
compose = Compose

||| Stop reason why tokenizer can't make more progress.
||| @ ComposeNotClosing carries the span of composition begin token in the
|||                     form of `(startLine, startCol), (endLine, endCol)`.
public export
data StopReason = NoRuleApply | ComposeNotClosing (Int, Int) (Int, Int)

export
Show StopReason where
    show NoRuleApply = "NoRuleApply"
    show (ComposeNotClosing start end) = "ComposeNotClosing " ++ show start ++ " " ++ show end

tokenise : (WithBounds a -> Bool) ->
           Tokenizer a ->
           (line, col : Int) -> List (WithBounds a) ->
           List Char ->
           (List (WithBounds a), StopReason, (Int, Int, List Char))
tokenise pred tokenizer line col acc str
    = case getFirstToken tokenizer str of
           Right (tok, line', col', rest) =>
                 if pred tok
                    then (reverse acc, NoRuleApply, (line, col, []))
                    -- assert total because getFirstToken must consume something
                    else assert_total (tokenise pred tokenizer line' col' (tok :: acc) rest)
           Left reason => (reverse acc, reason, (line, col, str))
  where
    countNLs : List Char -> Nat
    countNLs str = List.length (filter (== '\n') str)

    getCols : List Char -> Int -> Int
    getCols x c
        = case span (/= '\n') x of
               (incol, []) => c + cast (length incol)
               (incol, _) => cast (length incol)

    getFirstToken : Tokenizer a -> List Char ->
                    Either StopReason (WithBounds a, Int, Int, List Char)
    getFirstToken (Match lex fn) str
        = let Just (tok, rest) = scan lex [] str
                | _ => Left NoRuleApply
              line' = line + cast (countNLs tok)
              col' = getCols tok col in
              Right (MkBounded (fn (fastPack (reverse tok))) False line col line' col',
                    line', col', rest)
    getFirstToken (Compose begin tagger middleFn endFn fn) str
        = let Just (beginTok, rest) = scan begin [] str
                | _ => Left NoRuleApply
              line' = line + cast (countNLs beginTok)
              col' = getCols beginTok col
              tag = tagger $ fastPack beginTok
              middle = middleFn tag
              (midToks, NoRuleApply, (line'', col'', rest'')) =
                    tokenise (const False) middle line' col' [] rest
                | (_, reason, _) => Left reason
              end = endFn tag
              Just (endTok, rest''') = scan end [] rest''
                | _ => Left $ ComposeNotClosing (line, col) (line', col')
              line''' = line'' + cast (countNLs endTok)
              col''' = getCols endTok col''
              midToks' = MkBounded (fn tag midToks) False line col line''' col''' in
              Right (midToks', line''', col''', rest''')
    getFirstToken (Alt t1 t2) str
        = case getFirstToken t1 str of
               Right result => Right result
               Left reason@(ComposeNotClosing _ _) => Left reason
               Left _ => getFirstToken t2 str

export
lexTo : (WithBounds a -> Bool) ->
        Tokenizer a ->
        String ->
        (List (WithBounds a), StopReason, (Int, Int, String))
lexTo pred tokenizer str
    = let (ts, reason, (l, c, str')) =
              tokenise pred tokenizer 0 0 [] (fastUnpack str) in
          (ts, reason, (l, c, fastPack str'))

||| Given a tokenizer and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the string
||| where there are no recognised tokens.
export
lex : Tokenizer a -> String -> (List (WithBounds a), StopReason, (Int, Int, String))
lex tokenizer str = lexTo (const False) tokenizer str
