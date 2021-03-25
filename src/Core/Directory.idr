module Core.Directory

import Core.Context
import Core.Context.Log
import Core.Core
import Core.FC
import Core.Name
import Core.Options
import Libraries.Utils.Path

import Data.List
import Data.Strings
import Data.Maybe

import System.Directory
import System.File
import System.Info

%default total

-- Return the name of the first file available in the list
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
         let fs = map (\p => p </> fname) (data_dirs d)
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

-- Look for a library file required by a code generator. Look in the
-- library directories, and in the lib/ subdirectoriy of all the 'extra import'
-- directories
export
findLibraryFile : {auto c : Ref Ctxt Defs} ->
                  String -> Core String
findLibraryFile fname
    = do d <- getDirs
         let fs = map (\p => p </> fname)
                      (lib_dirs d ++ map (\x => x </> "lib")
                                         (extra_dirs d))
         Just f <- firstAvailable fs
            | Nothing => throw (InternalError ("Can't find library " ++ fname))
         pure f

-- Given a namespace, return the full path to the checked module,
-- looking first in the build directory then in the extra_dirs
export
nsToPath : {auto c : Ref Ctxt Defs} ->
           FC -> ModuleIdent -> Core (Either Error String)
nsToPath loc ns
    = do d <- getDirs
         let fnameBase = joinPath (reverse $ unsafeUnfoldModuleIdent ns)
         let fs = map (\p => p </> fnameBase <.> "ttc")
                      ((build_dir d </> "ttc") :: extra_dirs d)
         Just f <- firstAvailable fs
            | Nothing => pure (Left (ModuleNotFound loc ns))
         pure (Right f)

-- Given a namespace, return the full path to the source module (if it
-- exists in the working directory)
export
nsToSource : {auto c : Ref Ctxt Defs} ->
             FC -> ModuleIdent -> Core String
nsToSource loc ns
    = do d <- getDirs
         let fnameOrig = joinPath (reverse $ unsafeUnfoldModuleIdent ns)
         let fnameBase = maybe fnameOrig (\srcdir => srcdir </> fnameOrig) (source_dir d)
         let fs = map (\ext => fnameBase <.> ext)
                      [".idr", ".lidr", ".yaff", ".org", ".md"]
         Just f <- firstAvailable fs
            | Nothing => throw (ModuleNotFound loc ns)
         pure f

-- Given a filename in the working directory + source directory, return the correct
-- namespace for it
export
pathToNS : String -> Maybe String -> String -> Core ModuleIdent
pathToNS wdir sdir fname =
  let
    sdir = fromMaybe "" sdir
    base = if isAbsolute fname then wdir </> sdir else sdir
  in
    case Path.dropBase base fname of
      Nothing => throw (UserError (
          "Source file "
        ++ show fname
        ++ " is not in the source directory "
        ++ show (wdir </> sdir)))
      Just relPath =>
        pure $ unsafeFoldModuleIdent $ reverse $ splitPath $ Path.dropExtension relPath

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
    = do d <- getDirs
         let bdir = build_dir d </> "ttc"
         let ns = reverse $ fromMaybe [] $ tail' $ unsafeUnfoldModuleIdent ns -- first item is file name
         let ndir = joinPath ns
         Right _ <- coreLift $ mkdirAll (bdir </> ndir)
            | Left err => throw (FileErr (build_dir d </> ndir) err)
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
    = do ns <- getNS
         d <- getDirs
         -- Get its namespace from the file relative to the working directory
         -- and generate the ttc file from that
         ns <- pathToNS (working_dir d) (source_dir d) inp
         let fname = joinPath (reverse $ unsafeUnfoldModuleIdent ns) <.> ext
         let bdir = build_dir d
         pure $ bdir </> "ttc" </> fname

-- Given a root executable name, return the name in the build directory
export
getExecFileName : {auto c : Ref Ctxt Defs} -> String -> Core String
getExecFileName efile
    = do d <- getDirs
         pure $ build_dir d </> efile

getEntries : Directory -> IO (List String)
getEntries d
    = do Right f <- dirEntry d
             | Left err => pure []
         ds <- assert_total $ getEntries d
         pure (f :: ds)

dirEntries : String -> IO (Either FileError (List String))
dirEntries dir
    = do Right d <- openDir dir
             | Left err => pure (Left err)
         ds <- getEntries d
         closeDir d
         pure (Right ds)

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
        = do Right files <- dirEntries dir
                 | Left err => pure Nothing
             let Just f = find (\f => extension f == Just "ipkg") files
                 | Nothing => case splitParent dir of
                                   Just (parent, end) => findIpkgFile' parent (end </> up)
                                   Nothing => pure Nothing
             pure $ Just (dir, f, up)
