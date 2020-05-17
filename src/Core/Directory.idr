module Core.Directory

import Core.Context
import Core.Core
import Core.FC
import Core.Name
import Core.Options

import Data.List
import Data.Strings

import System.Directory
import System.File
import System.Info

%default total

fullPath : String -> List String
fullPath fp = filter (/="") $ split (==sep) fp

dropExtension : String -> String
dropExtension fname
    = case span (/= '.') (reverse fname) of
           (all, "") => -- no extension
               reverse all
           (ext, root) =>
               -- assert that root can't be empty
               reverse (assert_total (strTail root))

-- Return the name of the first file available in the list
firstAvailable : List String -> Core (Maybe String)
firstAvailable [] = pure Nothing
firstAvailable (f :: fs)
    = do Right ok <- coreLift $ openFile f Read
               | Left err => firstAvailable fs
         coreLift $ closeFile ok
         pure (Just f)

export
readDataFile : {auto c : Ref Ctxt Defs} ->
               String -> Core String
readDataFile fname
    = do d <- getDirs
         let fs = map (\p => p ++ dirSep ++ fname) (data_dirs d)
         Just f <- firstAvailable fs
            | Nothing => throw (InternalError ("Can't find data file " ++ fname ++
                                               " in any of " ++ show fs))
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
         let fs = map (\p => p ++ dirSep ++ fname)
                      (lib_dirs d ++ map (\x => x ++ dirSep ++ "lib")
                                         (extra_dirs d))
         Just f <- firstAvailable fs
            | Nothing => throw (InternalError ("Can't find library " ++ fname))
         pure f

-- Given a namespace, return the full path to the checked module,
-- looking first in the build directory then in the extra_dirs
export
nsToPath : {auto c : Ref Ctxt Defs} ->
           FC -> List String -> Core (Either Error String)
nsToPath loc ns
    = do d <- getDirs
         let fnameBase = showSep dirSep (reverse ns)
         let fs = map (\p => p ++ dirSep ++ fnameBase ++ ".ttc")
                      ((build_dir d ++ dirSep ++ "ttc") :: extra_dirs d)
         Just f <- firstAvailable fs
            | Nothing => pure (Left (ModuleNotFound loc ns))
         pure (Right f)

-- Given a namespace, return the full path to the source module (if it
-- exists in the working directory)
export
nsToSource : {auto c : Ref Ctxt Defs} ->
             FC -> List String -> Core String
nsToSource loc ns
    = do d <- getDirs
         let fnameOrig = showSep dirSep (reverse ns)
         let fnameBase = maybe fnameOrig (\srcdir => srcdir ++ dirSep ++ fnameOrig) (source_dir d)
         let fs = map (\ext => fnameBase ++ ext)
                      [".idr", ".lidr", ".yaff", ".org", ".md"]
         Just f <- firstAvailable fs
            | Nothing => throw (ModuleNotFound loc ns)
         pure f

-- Given a filename in the working directory + source directory, return the correct
-- namespace for it
export
pathToNS : String -> Maybe String -> String -> List String
pathToNS wdir sdir fname
    = let wsplit = splitSep wdir
          ssplit = maybe [] splitSep sdir
          fsplit = splitSep fname
          wdrop = dropDir wsplit fsplit fsplit
       in
      dropDir ssplit wdrop wdrop
  where
    dropDir : List String -> List String -> List String -> List String
    dropDir dir orig [] = []
    dropDir dir orig (x :: xs)
        = if dir == xs
             then [x]
             else x :: dropDir dir orig xs

    splitSep : String -> List String
    splitSep fname
        = case span (/=sep) fname of
               (end, "") => [dropExtension end]
               (mod, rest) => assert_total (splitSep (strTail rest)) ++ [mod]

-- Create subdirectories, if they don't exist
export
mkdirs : List String -> IO (Either FileError ())
mkdirs [] = pure (Right ())
mkdirs ("." :: ds) = mkdirs ds
mkdirs ("" :: ds) = mkdirs ds
mkdirs (d :: ds)
    = do ok <- changeDir d
         if ok
            then do mkdirs ds
                    changeDir ".."
                    pure (Right ())
            else do Right _ <- createDir d
                        | Left err => pure (Left err)
                    ok <- changeDir d
                    mkdirs ds
                    changeDir ".."
                    pure (Right ())

isDirSep : Char -> Bool
isDirSep c = cast c == dirSep

export
splitDir : String -> List String
splitDir = split isDirSep

-- Given a namespace (i.e. a module name), make the build directory for the
-- corresponding ttc file
export
makeBuildDirectory : {auto c : Ref Ctxt Defs} ->
                     List String -> Core ()
makeBuildDirectory ns
    = do d <- getDirs
         let bdir = splitDir $ build_dir d
         let ndirs = case ns of
                          [] => []
                          (n :: ns) => ns -- first item is file name
         let fname = showSep dirSep (reverse ndirs)
         Right _ <- coreLift $ mkdirs (bdir ++ "ttc" :: reverse ndirs)
            | Left err => throw (FileErr (build_dir d ++ dirSep ++ fname) err)
         pure ()

export
makeExecDirectory : {auto c : Ref Ctxt Defs} ->
                    Core ()
makeExecDirectory
    = do d <- getDirs
         let edir = splitDir $ exec_dir d
         Right _ <- coreLift $ mkdirs edir
            | Left err => throw (FileErr (exec_dir d) err)
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
         let ns = pathToNS (working_dir d) (source_dir d) inp
         let fname = showSep dirSep (reverse ns) ++ ext
         let bdir = build_dir d
         pure $ bdir ++ dirSep ++ "ttc" ++ dirSep ++ fname

-- Given a root executable name, return the name in the build directory
export
getExecFileName : {auto c : Ref Ctxt Defs} -> String -> Core String
getExecFileName efile
    = do d <- getDirs
         pure $ build_dir d ++ dirSep ++ efile

getEntries : Directory -> IO (List String)
getEntries d
    = do Right f <- dirEntry d
             | Left err => pure []
         ds <- assert_total $ getEntries d
         pure (f :: ds)

dirEntries : String -> IO (Either FileError (List String))
dirEntries dir
    = do Right d <- dirOpen dir
             | Left err => pure (Left err)
         ds <- getEntries d
         dirClose d
         pure (Right ds)

findIpkg : List String -> Maybe String
findIpkg [] = Nothing
findIpkg (f :: fs)
    = if isSuffixOf ".ipkg" f
         then Just f
         else findIpkg fs

allDirs : String -> List String -> List (String, List String)
allDirs path [] = []
allDirs path ("" :: ds) = ("/", ds) :: allDirs path ds
allDirs path (d :: ds)
    = let d' = path ++ strCons sep d in
          (d', ds) :: allDirs d' ds

-- Find an ipkg file in any of the directories above this one
-- returns the directory, the ipkg file name, and the directories we've
-- gone up
export
findIpkgFile : IO (Maybe (String, String, List String))
findIpkgFile
    = do Just dir <- currentDir
              | Nothing => pure Nothing
         -- 'paths' are the paths to look for an .ipkg, in order
         let paths = reverse (allDirs "" (splitDir dir))
         res <- firstIpkg paths
         pure res
  where
    firstIpkg : List (String, List String) ->
                IO (Maybe (String, String, List String))
    firstIpkg [] = pure Nothing
    firstIpkg ((d, up) :: ds)
        = do Right files <- dirEntries d
                   | Left err => pure Nothing
             let Just f = findIpkg files
                   | Nothing => firstIpkg ds
             pure $ Just (d, f, up)
