module Parser.Package

import public Parser.Lexer.Package
import public Parser.Rule.Package
import public Text.Lexer
import public Text.Parser
import public Parser.Support

import System.File
import Utils.Either

%default total

export
runParser : String -> Rule ty -> Either (ParseError Token) ty
runParser str p
    = do toks   <- mapError LexFail $ lex str
         parsed <- mapError toGenericParsingError $ parse p toks
         Right (fst parsed)

export
covering
parseFile : (fn : String) -> Rule ty -> IO (Either (ParseError Token) ty)
parseFile fn p
    = do Right str <- readFile fn
             | Left err => pure (Left (FileFail err))
         pure (runParser str p)
