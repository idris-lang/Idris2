module TTImp.Interactive.Completion

import Core.Context
import Core.Context.Log
import Core.Core

import Idris.Parser
import Idris.REPL.IDEIndex
import Idris.REPL.Opts
import Idris.Syntax

import Data.String

import Libraries.Data.WithDefault

||| A single suggested completion.
||| If import_ is Just, it's a module namespace that has to be imported
||| to access the name.
public export
record Completion where
  constructor MkCompletion
  name    : String
  import_ : Maybe String

simpleCompletion : String -> Completion
simpleCompletion = flip MkCompletion Nothing

autoImportCompletion : String -> String -> Completion
autoImportCompletion n = MkCompletion n . Just

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
                 {auto o : Ref ROpts REPLOpts} ->
                 (pref : String) -> Core (List Completion)
nameCompletion pref = do
  log "ide-mode.completion" 30 $ "Looking at name completions for \{show pref}"

  ctxtDefs <- get Ctxt
  let cns = currentNS ctxtDefs

  -- Look among already imported names:
  ctxtNamesWithPrefix <- filter hasPrefix <$> allNames (gamma ctxtDefs)
  ctxtVisibleGDefs <- filter (isVisible cns) <$> mapMaybeM (lookupName ctxtDefs) ctxtNamesWithPrefix
  let ctxtVisibleNames = nub $ fst <$> ctxtVisibleGDefs
  let ctxCompletions = simpleCompletion . unqualName <$> ctxtVisibleNames

  -- If we have an index, look there as well
  Just ideIndex <- ideIndex <$> get ROpts
    | Nothing => pure ctxCompletions
  let idxDefs = filter (hasPrefix . fullname) $ indexedDefs ideIndex
  let idxNames = filter (not . (`elem` ctxtVisibleNames)) $ fullname <$> idxDefs
  let idxCompletions = autoImport <$> idxNames
  pure (ctxCompletions ++ idxCompletions)

  where
    unqualName : Name -> String
    unqualName = nameRoot . snd . splitNS

    autoImport : Name -> Completion
    autoImport n = autoImportCompletion (unqualName n) (show $ fst $ splitNS n)

    hasPrefix : Name -> Bool
    hasPrefix = isPrefixOf pref . unqualName

    lookupName : Defs -> Name -> Core (Maybe (Name, GlobalDef))
    lookupName defs nsn = do
      Just def <- lookupCtxtExact nsn (gamma defs)
        | Nothing => pure Nothing
      pure (Just (nsn, def))

    isVisible : Namespace -> (Name, GlobalDef) -> Bool
    isVisible cns gdef = visibleIn cns (fst gdef) (collapseDefault $ visibility (snd gdef))


||| Completion among a list of constants
oneOfCompletion : String -> List String -> Maybe (List Completion)
oneOfCompletion pref candidates = do
    let cs@(_ :: _) = filter (pref `isPrefixOf`) candidates
      | _ => Nothing
    pure $ simpleCompletion <$> cs

||| Pragma completion receives everything on the line following the % character
||| and completes either the pragma itself of one of its arguments
||| %def         -> %default
||| %default to  -> %default total
||| %logging "id -> %logging "ide-mode.(...)" with all the valid topics!
pragmaCompletion : {auto c : Ref Ctxt Defs} ->
                   {auto o : Ref ROpts REPLOpts} ->
                   (prag : Maybe KwPragma) -> (pref : String) ->
                   Core (Maybe (String, List Completion))
pragmaCompletion Nothing pref = pure $ do
  let ps@(_ :: _) = flip List.mapMaybe allPragmas $ \ prag => do
                      let prag = show prag
                      guard ("%" ++ pref `isPrefixOf` prag)
                      pure prag
    | _ => Nothing
  pure ("", simpleCompletion <$> ps)
pragmaCompletion (Just kw) pref = go (pragmaArgs kw) (break isSpace pref) where

  go : List PragmaArg -> (String, String) -> Core (Maybe (String, List Completion))
  go (AName {} :: _) (here, "") = do
    ns@(_ :: _) <- nameCompletion here
      | _ => pure Nothing
    pure (Just ("", ns))
  go (AnOnOff :: _) (here, "") = pure (("",) <$> oneOfCompletion here ["on", "off"])
  go (AnOptionalLoggingTopic :: _) (here, "") = do
    let StrCons '"' here = strM here
      | _ => pure Nothing
    let lvls@(_ :: _) = filter ((here `isPrefixOf`) . fst) knownTopics
      | _ => pure Nothing
    pure (Just ("", map (simpleCompletion . show . fst) lvls))
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
             {auto o : Ref ROpts REPLOpts} ->
             (line : String) -> Core (Maybe (String, List Completion))
completion line = do
  let Just (ctxt, task) = parseTask line
    | _ => pure Nothing
  case task of
    NameCompletion pref => (Just . (ctxt,)) <$> nameCompletion pref
    PragmaCompletion mprag pref => map (mapFst (ctxt ++)) <$> pragmaCompletion mprag pref
    CommandCompletion pref => case words pref of
      ["logging"] => pure $ Just (ctxt ++ ":logging", map (simpleCompletion . (" " ++) . show . fst) knownTopics)
      [pref] => let commands = concatMap fst parserCommandsForHelp in
                pure $ map ((ctxt,) . map ({ name $= (":" ++)})) $ oneOfCompletion pref commands
      ["logging", w] => pure $ map (ctxt ++ ":logging ",) (oneOfCompletion w (map (show . fst) knownTopics))
      _ => pure Nothing
