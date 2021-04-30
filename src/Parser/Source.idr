module Parser.Source

import public Parser.Lexer.Source
import public Parser.Rule.Source
import public Parser.Unlit

import Core.Core
import Core.Name
import Core.Metadata
import Core.FC
import System.File
import Libraries.Utils.Either

%default total

export
runParserTo : {e : _} ->
              (fname : String) ->
              Maybe LiterateStyle -> Lexer ->
              String -> Grammar SemanticDecorations Token e ty -> Either Error (SemanticDecorations, ty)
runParserTo fname lit reject str p
    = do str    <- mapError (fromLitError fname) $ unlit lit str
         toks   <- mapError (fromLexError fname) $ lexTo reject str
         (decs, (parsed, _)) <- mapError (fromParsingError fname) $ parseWith p toks
         Right (decs, parsed)

export
runParser : {e : _} ->
            (fname : String) -> Maybe LiterateStyle -> String ->
            Grammar SemanticDecorations Token e ty -> Either Error (SemanticDecorations, ty)
runParser fname lit = runParserTo fname lit (pred $ const False)

export covering
parseFile : (fname : String) -> Rule ty -> IO (Either Error (SemanticDecorations, ty))
parseFile fname p
    = do Right str <- readFile fname
             | Left err => pure (Left (FileErr fname err))
         pure (runParser fname (isLitFile fname) str p)
