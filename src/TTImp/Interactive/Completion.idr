module TTImp.Interactive.Completion

import Core.Context
import Core.Context.Log
import Core.Core

import Idris.Syntax
import Idris.Parser

import Data.String

||| Completion tasks are varied:
||| are we trying to fill in a name, a REPL command, a pragma?
data Task
  = NameCompletion    String
  | CommandCompletion String
  | PragmaCompletion  (Maybe KwPragma) String

||| Completion receives the whole line it is supposed to work on.
||| We start by trying to make sense of it as:
||| 1. an ignored prefix (e.g. 'map' in 'map rever', '  ' in '  %def')
||| 2. a completion task
parseTask : (line : String) -> Maybe (String, Task)
parseTask line =
  let (indnt, focus) = break (not . isSpace) line in
  case strM focus of
    StrCons '%' rest => case break isSpace rest of
        (pref, "") => pure (indnt, PragmaCompletion Nothing pref)
        (prag, rest) => do let prag = "%" ++ prag
                           let (spcs, rest) = break (not . isSpace) rest
                           let [kwprag] = filter ((prag ==) . show) allPragmas
                            | _ => Nothing
                           pure (concat {t = List} [indnt, prag, spcs]
                                , PragmaCompletion (Just kwprag) rest)
    StrCons ':' rest => pure (indnt, CommandCompletion rest)
    _ => let ("", rest) = bimap Prelude.reverse Prelude.reverse
                        $ break (\ x => not (isAlphaNum x || x > chr 160))
                        $ Prelude.reverse line
              | (pref, rest) => pure (rest, NameCompletion pref)
         in Nothing

||| Name completion receives the prefix of the name to be completed
nameCompletion : {auto c : Ref Ctxt Defs} ->
                 (pref : String) -> Core (List String)
nameCompletion pref = do
  log "ide-mode.completion" 30 $ "Looking at name completions for \{show pref}"
  defs <- get Ctxt
  let cns = currentNS defs
  nms <- flip mapMaybeM !(allNames (gamma defs)) $ \ nsn => do
    -- the name better be a completion
    log "ide-mode.completion" 50 $ "Looking at \{show nsn}"
    let (ns, n) = splitNS nsn
    let True = pref `isPrefixOf` nameRoot n
      | False => pure Nothing
    -- and it better be visible
    Just def <- lookupCtxtExact nsn (gamma defs)
      | Nothing => pure Nothing
    let True = visibleIn cns nsn (visibility def)
      | False => pure Nothing
    pure (Just n)
  pure (map show $ nub nms)

||| Completion among a list of constants
oneOfCompletion : String -> List String -> Maybe (List String)
oneOfCompletion pref candidates = do
    let cs@(_ :: _) = filter (pref `isPrefixOf`) candidates
      | _ => Nothing
    pure cs

||| Pragma completion receives everything on the line following the % character
||| and completes either the pragma itself of one of its arguments
||| %def         -> %default
||| %default to  -> %default total
||| %logging "id -> %logging "ide-mode.(...)" with all the valid topics!
pragmaCompletion : {auto c : Ref Ctxt Defs} ->
                   (prag : Maybe KwPragma) -> (pref : String) ->
                   Core (Maybe (String, List String))
pragmaCompletion Nothing pref = pure $ do
  let ps@(_ :: _) = flip List.mapMaybe allPragmas $ \ prag => do
                      let prag = show prag
                      guard ("%" ++ pref `isPrefixOf` prag)
                      pure prag
    | _ => Nothing
  pure ("", ps)
pragmaCompletion (Just kw) pref = go (pragmaArgs kw) (break isSpace pref) where

  go : List PragmaArg -> (String, String) -> Core (Maybe (String, List String))
  go (AName{} :: _) (here, "") = do
    ns@(_ :: _) <- nameCompletion here
      | _ => pure Nothing
    pure (Just ("", ns))
  go (AnOnOff :: _) (here, "") = pure (("",) <$> oneOfCompletion here ["on", "off"])
  go (AnOptionalLoggingTopic :: _) (here, "") = do
    let StrCons '"' here = strM here
      | _ => pure Nothing
    let lvls@(_ :: _) = filter ((here `isPrefixOf`) . fst) knownTopics
      | _ => pure Nothing
    pure (Just ("", map (show . fst) lvls))
  go (ALangExt :: _) (here, "") = pure (("",) <$> oneOfCompletion here (map show allLangExts))
  go (ATotalityLevel :: _) (here, "") = pure (("",) <$> oneOfCompletion here ["partial", "covering", "total"])
  go (_ :: args) (skip, rest) =
    let (indnt, rest) = break (not . isSpace) rest in
    map (mapFst ((skip ++ indnt) ++)) <$> go args (break isSpace rest)
  go _ (_, _) = pure Nothing

||| Completion receives the full line and returns
||| 1. the ignored prefix
||| 2. the list of possible completions
export
completion : {auto c : Ref Ctxt Defs} ->
             (line : String) -> Core (Maybe (String, List String))
completion line = do
  let Just (ctxt, task) = parseTask line
    | _ => pure Nothing
  case task of
    NameCompletion pref => (Just . (ctxt,)) <$> nameCompletion pref
    PragmaCompletion mprag pref => map (mapFst (ctxt ++)) <$> pragmaCompletion mprag pref
    CommandCompletion pref =>
      let commands = concatMap fst parserCommandsForHelp in
      pure $ map ((ctxt,) . map (":" ++)) $ oneOfCompletion pref commands
