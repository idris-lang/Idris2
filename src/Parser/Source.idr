module Parser.Source

import public Parser.Lexer.Source
import public Parser.Rule.Source
import public Parser.Unlit

import Core.Core
import Core.Name
import Core.Metadata
import Core.FC

import System.File

%default total

export
runParserTo : {e : _} ->
              (origin : OriginDesc) ->
              Maybe LiterateStyle -> Lexer ->
              String -> Grammar ParsingState Token e ty ->
              Either Error (List Warning, State, ty)
runParserTo origin lit reject str p
    = do str        <- mapFst (fromLitError origin) $ unlit lit str
         (cs, toks) <- mapFst (fromLexError origin) $ lexTo reject str
         (decs, ws, (parsed, _)) <- mapFst (fromParsingErrors origin) $ parseWith p toks
         let cs : SemanticDecorations
                = cs <&> \ c => ((origin, start c, end c), Comment, Nothing)
         let ws = ws <&> \ (mb, warn) =>
                    let mkFC = \ b => MkFC origin (startBounds b) (endBounds b)
                    in ParserWarning (maybe EmptyFC mkFC mb) warn
         let state : State
             state = { decorations $= (cs++) } (toState decs)
         pure (ws, state, parsed)

export
runParser : {e : _} ->
            (origin : OriginDesc) -> Maybe LiterateStyle -> String ->
            Grammar ParsingState Token e ty ->
            Either Error (List Warning, State, ty)
runParser origin lit = runParserTo origin lit (pred $ const False)

export covering
parseFile : (fname : String)
         -> (origin : OriginDesc)
         -> Rule ty
         -> IO (Either Error (List Warning, State, ty))
parseFile fname origin p
    = do Right str <- readFile fname
             | Left err => pure (Left (FileErr fname err))
         pure (runParser origin (isLitFile fname) str p)
