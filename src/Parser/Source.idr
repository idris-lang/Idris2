module Parser.Source

import public Parser.Lexer.Source
import public Parser.Rule.Source
import public Parser.Unlit
import public Text.Lexer
import public Text.Parser

import System.File
import Utils.Either

%default total

export
runParserTo : {e : _} ->
              Maybe LiterateStyle -> (TokenData SourceToken -> Bool) ->
              String -> Grammar (TokenData SourceToken) e ty -> Either ParseError ty
runParserTo lit pred str p
    = do str    <- mapError LitFail $ unlit lit str
         toks   <- mapError LexFail $ lexTo pred str
         parsed <- mapError mapParseError $ parse p toks
         Right (fst parsed)

export
runParser : {e : _} ->
            Maybe LiterateStyle -> String -> Grammar (TokenData SourceToken) e ty -> Either ParseError ty
runParser lit = runParserTo lit (const False)

export
parseFile : (fn : String) -> SourceRule ty -> IO (Either ParseError ty)
parseFile fn p
    = do Right str <- readFile fn
             | Left err => pure (Left (FileFail err))
         pure (runParser (isLitFile fn) str p)
