module Idris.REPL.IDEIndex

import Core.Binary
import Core.Core
import Core.Context
import Core.Name.Namespace
import Core.UnifyState
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

||| Recursively finds all TTC files in the given directory and returns
||| their full paths along with their corresponding namespaces.
findTtcFiles : String -> Core (List (String, Namespace))
findTtcFiles dir = go dir (mkNamespace "")
  where
    mkItem : String -> Namespace -> String -> (String, Namespace)
    mkItem dir ns f
      = ( dir </> f
        , maybe ns (mkNestedNamespace (Just ns)) (fileStem f)
        )

    go : String -> Namespace -> Core (List (String, Namespace))
    go dir ns = do
      Right entries <- coreLift $ listDir dir
        | Left _ => pure []
      let entries = filter (\f => not $ f == "." || f == "..") entries
      let ttcFiles = mkItem dir ns <$> filter (".ttc" `isSuffixOf`) entries
      let subdirs = filter (not . isInfixOf ".") entries
      subdirFiles <- concat <$> traverse
        (\dir' => go (dir </> dir') (mkNestedNamespace (Just ns) dir'))
        subdirs
      pure $ ttcFiles ++ subdirFiles

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

indexDefsOfTtc : (String, Namespace) -> Core (List IndexedDef)
indexDefsOfTtc (ttcFile, ttcModNS) = do
  _ <- newRef Ctxt !initDefs
  _ <- newRef UST initUState
  Just (syntaxInfo, _, imports) <- readFromTTC {extra = SyntaxInfo}
          False -- don't set nested namespaces (irrelevant for us)
          EmptyFC
          False -- don't import as public (irrelevant to us)
          ttcFile -- file to read
          (nsAsModuleIdent ttcModNS) -- module identifier
          (ttcModNS) -- "importAs" (irrelevant to us)
    | Nothing => pure []

  modNS <- nsAsModuleIdent <$> getNS
  names <- filter (isJust . userNameRoot) <$> allNames (gamma !(get Ctxt))
  visibleDefs <- mapMaybeM defIfVisible names
  pure $ MkIndexedDef ttcModNS <$> visibleDefs

||| Builds an IDE index from all TTC files found in the given package directories.
export
mkIdeIndex : List String -> Core IDEIndex
mkIdeIndex pkg_dirs = do
  let pkgTtcDirs = pkg_dirs <&> (</> show ttcVersion)
  pkgTtcFiles <- concat <$> traverse findTtcFiles pkgTtcDirs
  indexedDefs <- concat <$> traverse indexDefsOfTtc pkgTtcFiles
  pure $ MkIDEIndex indexedDefs
