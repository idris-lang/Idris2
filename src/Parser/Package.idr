module Parser.Package

import public Parser.Lexer.Package
import public Parser.Rule.Package
import public Libraries.Text.Lexer
import public Libraries.Text.Parser
import public Parser.Support

import Core.Core
import Core.FC
import System.File

%default total

export
runParser : (fname : String) -> (str : String) -> Rule ty -> Either Error ty
runParser fname str p
    = do toks   <- mapFst (\err => fromLexError
                     (PhysicalPkgSrc fname) (NoRuleApply, err)) $ lex str
         (_, val, _) <- mapFst (fromParsingErrors (PhysicalPkgSrc fname)) $ parse p toks
         Right val

export
covering
parseFile : (fname : String) -> Rule ty -> IO (Either Error ty)
parseFile fname p
    = do Right str <- readFile fname
             | Left err => pure (Left (FileErr fname err))
         pure (runParser fname str p)
