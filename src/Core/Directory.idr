module Core.Directory

import Core.Binary
import Core.Context
import Core.Context.Log
import Core.Core
import Core.FC
import Core.Options

import Idris.Version

import Parser.Unlit

import Libraries.Data.Version
import Libraries.Utils.Path

import Data.List
import Data.Maybe

import System.Directory

%default total

------------------------------------------------------------------------
-- Package directories

export
pkgGlobalDirectory : {auto c : Ref Ctxt Defs} -> Core String
pkgGlobalDirectory =
  do d <- getDirs
     pure (prefix_dir d </> "idris2-" ++ showVersion False version)

export
pkgLocalDirectory : {auto c : Ref Ctxt Defs} -> Core String
pkgLocalDirectory =
  do d <- getDirs
     Just srcdir <- coreLift currentDir
       | Nothing => throw (InternalError "Can't get current directory")
     pure $ srcdir </> depends_dir d

------------------------------------------------------------------------
-- TTC directories

export
ttcBuildDirectory : {auto c : Ref Ctxt Defs} -> Core String
ttcBuildDirectory =
  do d <- getDirs
     pure (build_dir d </> "ttc" </> show ttcVersion)

export
libInstallDirectory : {auto c : Ref Ctxt Defs} -> String -> Core String
libInstallDirectory lib =
  do gbdir <- pkgGlobalDirectory
     pure (gbdir </> lib)

export
ttcInstallDirectory : {auto c : Ref Ctxt Defs} -> String -> Core String
ttcInstallDirectory lib =
  do libDir <- libInstallDirectory lib
     pure (libDir </> show ttcVersion)

export
srcInstallDirectory : {auto c : Ref Ctxt Defs} -> String -> Core String
srcInstallDirectory = libInstallDirectory

export
extraSearchDirectories : {auto c : Ref Ctxt Defs} -> Core (List String)
extraSearchDirectories =
  do d <- getDirs
     pure (map (</> show ttcVersion) (extra_dirs d ++ package_dirs d))

------------------------------------------------------------------------

public export
data IdrSrcExt = E_idr | E_lidr | E_yaff | E_org | E_md

public export
Eq IdrSrcExt where
  E_idr  == E_idr  = True
  E_lidr == E_lidr = True
  E_yaff == E_yaff = True
  E_org  == E_org  = True
  E_md   == E_md   = True
  _      == _      = False

public export
Show IdrSrcExt where
  show E_idr  = "idr"
  show E_lidr = "lidr"
  show E_yaff = "yaff"
  show E_org  = "org"
  show E_md   = "md"

||| This does not include the complete set of literate extensions as supported by Idris.
public export
listOfExtensions : List IdrSrcExt
listOfExtensions = [E_idr, E_lidr, E_yaff, E_org, E_md]

||| List of valid extensions in Idris as strings.
|||
||| Extensions have a leading "." separator *and* may include multiple extensions to support literate mode extensions for the form ".org.idr".
|||
public export
listOfExtensionsStr : List String
listOfExtensionsStr = listOfExtensionsLiterate ++ [".yaff", ".idr"]

||| Given a path, removes trailing separators and current directory identifiers, '.'.
cleanPath : String -> String
cleanPath = show . the (Path -> Path) { hasTrailSep := False, body $= filter (/= CurDir) } . parse

||| Return the basename and extension used *if* given filename is a valid idris filename.
|||
||| Extensions are returned with a leading "." separator.
export
splitIdrisFileName : String -> Maybe (String, String)
splitIdrisFileName fname
    = hasLitFileExt fname <|> isPureCode

  where
    isPureCode : Maybe (String, String)
    isPureCode
      = let (bname, ext) = splitFileName fname in
        do guard (ext == "idr")
           pure (bname, ".idr")


-- Return the name of the first file available in the list
-- Used in LSP.
export
firstAvailable : {auto c : Ref Ctxt Defs} ->
                 List String -> Core (Maybe String)
firstAvailable [] = pure Nothing
firstAvailable (f :: fs)
    = do log "import.file" 30 $ "Attempting to read " ++ f
         Right ok <- coreLift $ openFile f Read
               | Left err => firstAvailable fs
         coreLift $ closeFile ok
         pure (Just f)

export
covering
findDataFile : {auto c : Ref Ctxt Defs} ->
               String -> Core String
findDataFile fname
    = do d <- getDirs
         let fs = map (\p => cleanPath $ p </> fname) (data_dirs d)
         Just f <- firstAvailable fs
            | Nothing => throw (InternalError ("Can't find data file " ++ fname ++
                                               " in any of " ++ show fs))
         pure f

export
covering
readDataFile : {auto c : Ref Ctxt Defs} ->
               String -> Core String
readDataFile fname
    = do f <- findDataFile fname
         Right d <- coreLift $ readFile f
            | Left err => throw (FileErr f err)
         pure d

||| Look for a library file required by a code generator. Look in the
||| library directories, and in the lib/ subdirectory of all the 'extra import'
||| directories and the package directory roots.
export
findLibraryFile : {auto c : Ref Ctxt Defs} ->
                  String -> Core String
findLibraryFile fname
    = do d <- getDirs
         let packageLibs = libDirs (package_dirs d)
         let extraLibs = libDirs (extra_dirs d)
         let fs = map (\p => cleanPath $ p </> fname)
                      (lib_dirs d ++ packageLibs ++ extraLibs)
         Just f <- firstAvailable fs
            | Nothing => throw (InternalError ("Can't find library " ++ fname))
         pure f
    where
      libDirs : List String -> List String
      libDirs = map (\x => x </> "lib")

-- Given a namespace, return the full path to the checked module,
-- looking first in the build directory then in the extra_dirs
export
nsToPath : {auto c : Ref Ctxt Defs} ->
           FC -> ModuleIdent -> Core (Either Error String)
nsToPath loc ns
    = do bdir <- ttcBuildDirectory
         ttcs <- extraSearchDirectories
         let fnameBase = ModuleIdent.toPath ns
         let fs = map (\p => cleanPath $ p </> fnameBase <.> "ttc") (bdir :: ttcs)
         Just f <- firstAvailable fs
            | Nothing => pure (Left (ModuleNotFound loc ns))
         pure (Right f)

-- Given a namespace, return the path to the source module relative
-- to the working directory, if the module exists.
export
nsToSource : {auto c : Ref Ctxt Defs} ->
             FC -> ModuleIdent -> Core String
nsToSource loc ns
    = do d <- getDirs
         let fnameOrig = ModuleIdent.toPath ns
         let fnameBase = cleanPath $ maybe fnameOrig (\srcdir => srcdir </> fnameOrig) (source_dir d)
         let fs = map ((fnameBase ++)) listOfExtensionsStr
         Just f <- firstAvailable fs
            | Nothing => throw (ModuleNotFound loc ns)
         pure f


-- Given a filename in the working directory + source directory, return the correct
-- namespace for it
export
mbPathToNS : String -> Maybe String -> String -> Maybe ModuleIdent
mbPathToNS wdir sdir fname =
  let
    sdir = fromMaybe "" sdir
    base = if isAbsolute fname then wdir </> sdir else sdir
  in
    unsafeFoldModuleIdent . reverse . splitPath . Path.dropExtension
      <$> (Path.dropBase `on` cleanPath) base fname

export
corePathToNS : String -> Maybe String -> String -> Core ModuleIdent
corePathToNS wdir sdir fname = do
  let err = UserError $
          "Source file "
       ++ show fname
       ++ " is not in the source directory "
       ++ show (wdir </> fromMaybe "" sdir)
  maybe (throw err) pure (mbPathToNS wdir sdir fname)

export
ctxtPathToNS : {auto c : Ref Ctxt Defs} -> String -> Core ModuleIdent
ctxtPathToNS fname = do
  defs <- get Ctxt
  let wdir = defs.options.dirs.working_dir
  let sdir = defs.options.dirs.source_dir
  corePathToNS wdir sdir fname

dirExists : String -> IO Bool
dirExists dir = do Right d <- openDir dir
                       | Left _ => pure False
                   closeDir d
                   pure True

-- Create subdirectories, if they don't exist
export
covering
mkdirAll : String -> IO (Either FileError ())
mkdirAll dir = if parse dir == emptyPath
                  then pure (Right ())
                  else do exist <- dirExists dir
                          if exist
                             then pure (Right ())
                             else do Right () <- case parent dir of
                                          Just parent => mkdirAll parent
                                          Nothing => pure (Right ())
                                        | err => pure err
                                     createDir dir

-- Given a namespace (i.e. a module name), make the build directory for the
-- corresponding ttc file
export
covering
makeBuildDirectory : {auto c : Ref Ctxt Defs} ->
                     ModuleIdent -> Core ()
makeBuildDirectory ns
    = do bdir <- ttcBuildDirectory
         let ns = reverse $ fromMaybe [] $ tail' $ unsafeUnfoldModuleIdent ns -- first item is file name
         let ndir = joinPath ns
         Right _ <- coreLift $ mkdirAll (bdir </> ndir)
            | Left err => throw (FileErr (bdir </> ndir) err)
         pure ()

export
covering
ensureDirectoryExists : String -> Core ()
ensureDirectoryExists dir
    = do Right _ <- coreLift $ mkdirAll dir
            | Left err => throw (FileErr dir err)
         pure ()

-- Given a source file, return the name of the ttc file to generate
export
getTTCFileName : {auto c : Ref Ctxt Defs} ->
                 String -> String -> Core String
getTTCFileName inp ext
    = do -- Get its namespace from the file relative to the working directory
         -- and generate the ttc file from that
         ns <- ctxtPathToNS inp
         let fname = ModuleIdent.toPath ns <.> ext
         bdir <- ttcBuildDirectory
         pure $ bdir </> fname

-- Given a source file, return the name of the corresponding object file.
-- As above, but without the build directory
export
getObjFileName : {auto c : Ref Ctxt Defs} ->
                 String -> String -> Core String
getObjFileName inp ext
    = do -- Get its namespace from the file relative to the working directory
         -- and generate the ttc file from that
         ns <- ctxtPathToNS inp
         let fname = ModuleIdent.toPath ns <.> ext
         pure $ fname

-- Given a root executable name, return the name in the build directory
export
getExecFileName : {auto c : Ref Ctxt Defs} -> String -> Core String
getExecFileName efile
    = do d <- getDirs
         pure $ build_dir d </> efile

-- Find an ipkg file in any of the directories above this one
-- returns the directory, the ipkg file name, and the directories we've
-- gone up
export
covering
findIpkgFile : IO (Maybe (String, String, String))
findIpkgFile
    = do Just dir <- currentDir
              | Nothing => pure Nothing
         res <- findIpkgFile' dir ""
         pure res
  where
    covering
    findIpkgFile' : String -> String -> IO (Maybe (String, String, String))
    findIpkgFile' dir up
        = do Right files <- listDir dir
                 | Left err => pure Nothing
             let Just f = find (\f => extension f == Just "ipkg") files
                 | Nothing => case splitParent dir of
                                   Just (parent, end) => findIpkgFile' parent (end </> up)
                                   Nothing => pure Nothing
             pure $ Just (dir, f, up)
