module Idris.REPL.IDEIndex

import Core.Binary
import Core.Core
import Core.Context
import Core.Name.Namespace
import Data.String
import Idris.Syntax
import Idris.Syntax.TTC
import Libraries.Data.WithDefault
import Libraries.Utils.Path
import System.Directory

||| An index of exported definitions from modules of available packages.
public export
record IDEIndex where
  constructor MkIDEIndex
  indexedDefs : List GlobalDef

findFiles : (String -> Bool) -> String -> Core (List String)
findFiles pred dir = do
  Right list <- coreLift $ listDir dir
    | Left _ => pure []
  let list = (dir </>) <$> filter (\f => not $ f == "." || f == "..") list
  concat <$> traverse go list
  where
    go : String -> Core (List String)
    go file = do
      if pred file
        then pure [file]
        else findFiles pred file

readTtcFile : Ref Ctxt Defs => String -> Core (TTCFile SyntaxInfo)
readTtcFile fname = do
  Right buffer <- coreLift $ readFromFile fname
    | Left err => throw (InternalError (fname ++ ": " ++ show err))
  bin <- newRef Bin buffer -- for reading the file into
  readTTCFile True fname Nothing bin

defIfVisible : Ref Ctxt Defs => Name -> Core (Maybe GlobalDef)
defIfVisible nsn = do
  defs <- get Ctxt
  let (ns, n) = splitNS nsn
  let cns = currentNS defs
  Just def <- lookupCtxtExact nsn (gamma defs)
    | Nothing => pure Nothing
  if visibleIn cns nsn (collapseDefault $ visibility def)
    then pure (Just def)
    else pure Nothing

allExportedDefs : Ref Ctxt Defs => Core (List GlobalDef)
allExportedDefs = do
  allNames <- allNames (gamma $ !(get Ctxt))
  let names = filter (isJust . userNameRoot) allNames
  mapMaybeM defIfVisible names

export
mkIdeIndex : List String -> Core IDEIndex
mkIdeIndex pkg_dirs = do
  let pkgTtcDirs = pkg_dirs <&> (</> show ttcVersion)
  pkgTtcFiles <- concat <$> traverse (findFiles $ isSuffixOf ".ttc") pkgTtcDirs
  _ <- newRef Ctxt !initDefs
  ttcs <- traverse readTtcFile pkgTtcFiles
  modNS <- nsAsModuleIdent <$> getNS
  traverse_ (\x => traverse_ (addGlobalDef modNS (currentNS x) Nothing) (context x)) ttcs
  pure $ MkIDEIndex (!allExportedDefs)
                                               
  