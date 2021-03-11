module Parser.Package

import public Parser.Lexer.Package
import public Parser.Rule.Package
import public Libraries.Text.Lexer
import public Libraries.Text.Parser
import public Parser.Support

import Core.Core
import System.File
import Libraries.Utils.Either

%default total

export
runParser : (fname : String) -> String -> Rule ty -> Either Error ty
runParser fname str p
    = do toks   <- mapError (\err => fromLexError fname (NoRuleApply, err)) $ lex str
         parsed <- mapError (fromParsingError fname) $ parse p toks
         Right (fst parsed)

export
covering
parseFile : (fname : String) -> Rule ty -> IO (Either Error ty)
parseFile fname p
    = do Right str <- readFile fname
             | Left err => pure (Left (FileErr fname err))
         pure (runParser fname str p)
