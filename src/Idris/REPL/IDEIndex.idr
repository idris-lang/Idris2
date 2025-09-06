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

public export
record IndexedDef where
  constructor MkIndexedDef
  moduleNS : Namespace
  def      : GlobalDef

||| An index of exported definitions from modules of available packages.
public export
record IDEIndex where
  constructor MkIDEIndex
  indexedDefs : List IndexedDef

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

indexDefsOfTtc : String -> Core (List IndexedDef)
indexDefsOfTtc ttcFile = do
  _ <- newRef Ctxt !initDefs
  ttc <- readTtcFile ttcFile
  let ttcModNS = currentNS ttc
  modNS <- nsAsModuleIdent <$> getNS
  traverse_ (addGlobalDef modNS ttcModNS Nothing) (context ttc)
  names <- filter (isJust . userNameRoot) <$> allNames (gamma !(get Ctxt))
  visibleDefs <- mapMaybeM defIfVisible names
  pure $ MkIndexedDef ttcModNS <$> visibleDefs

||| Builds an IDE index from all TTC files found in the given package directories.
export
mkIdeIndex : List String -> Core IDEIndex
mkIdeIndex pkg_dirs = do
  let pkgTtcDirs = pkg_dirs <&> (</> show ttcVersion)
  pkgTtcFiles <- concat <$> traverse (findFiles $ isSuffixOf ".ttc") pkgTtcDirs
  indexedDefs <- concat <$> traverse indexDefsOfTtc pkgTtcFiles
  pure $ MkIDEIndex indexedDefs
                                               
  