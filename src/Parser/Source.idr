module Parser.Source

import public Parser.Lexer.Source
import public Parser.Rule.Source
import public Parser.Unlit

import System.File
import Utils.Either

%default total

export
runParserTo : {e : _} ->
              Maybe LiterateStyle -> (TokenData Token -> Bool) ->
              String -> Grammar (TokenData Token) e ty -> Either (ParseError Token) ty
runParserTo lit pred str p
    = do str    <- mapError LitFail $ unlit lit str
         toks   <- mapError LexFail $ lexTo pred str
         parsed <- mapError toGenericParsingError $ parse p toks
         Right (fst parsed)

export
runParser : {e : _} ->
            Maybe LiterateStyle -> String -> Grammar (TokenData Token) e ty -> Either (ParseError Token) ty
runParser lit = runParserTo lit (const False)

export covering
parseFile : (fn : String) -> Rule ty -> IO (Either (ParseError Token) ty)
parseFile fn p
    = do Right str <- readFile fn
             | Left err => pure (Left (FileFail err))
         pure (runParser (isLitFile fn) str p)
