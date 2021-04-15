module Idris.SetOptions

import Core.Context
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Unify
import Libraries.Utils.Path
import Libraries.Data.List1 as Lib

import Idris.CommandLine
import Idris.Package.Types
import Idris.REPL
import Idris.Syntax
import Idris.Version

import IdrisPaths

import Data.List
import Data.So
import Data.Strings

import System
import System.Directory

%default covering

-- Get a list of all the candidate directories that match a package spec
-- in a given path. Return an empty list on file error (e.g. path not existing)
export
candidateDirs : String -> String -> PkgVersionBounds ->
                IO (List (String, Maybe PkgVersion))
candidateDirs dname pkg bounds
    = do Right d <- openDir dname
             | Left err => pure []
         getFiles d []
  where
    toVersion : String -> Maybe PkgVersion
    toVersion = map MkPkgVersion
              . traverse parsePositive
              . split (== '.')

    getVersion : String -> (String, Maybe PkgVersion)
    getVersion str =
      -- Split the dir name into parts concatenated by "-"
      -- treating the last part as the version number
      -- and the initial parts as the package name.
      -- For reasons of backwards compatibility, we also
      -- accept hyphenated directory names without a part
      -- corresponding to a version number.
      case Lib.unsnoc $ split (== '-') str of
        (Nil, last) => (last, Nothing)
        (init,last) =>
          case toVersion last of
            Just v  => (concat $ intersperse "-" init, Just v)
            Nothing => (str, Nothing)

    -- Return a list of paths that match the version spec
    -- (full name, version string)
    -- We'll order by version string that the highest version number is the
    -- one we use
    getFiles : Directory -> List (String, Maybe PkgVersion) ->
               IO (List (String, Maybe PkgVersion))
    getFiles d acc
        = do Right str <- dirEntry d
                   | Left err => pure (reverse acc)
             let (pkgdir, ver) = getVersion str
             if pkgdir == pkg && inBounds ver bounds
                then getFiles d (((dname </> str), ver) :: acc)
                else getFiles d acc

export
addPkgDir : {auto c : Ref Ctxt Defs} ->
            String -> PkgVersionBounds -> Core ()
addPkgDir p bounds
    = do defs <- get Ctxt
         let globaldir = prefix_dir (dirs (options defs)) </>
                               "idris2-" ++ showVersion False version
         let depends = depends_dir (dirs (options defs))
         Just srcdir <- coreLift currentDir
             | Nothing => throw (InternalError "Can't get current directory")
         let localdir = srcdir </> depends

         -- Get candidate directories from the global install location,
         -- and the local package directory
         locFiles <- coreLift $ candidateDirs localdir p bounds
         globFiles <- coreLift $ candidateDirs globaldir p bounds
         -- Look in all the package paths too
         let pkgdirs = (options defs).dirs.package_dirs
         pkgFiles <- coreLift $ traverse (\d => candidateDirs d p bounds) pkgdirs

         -- If there's anything locally, use that and ignore the global ones
         let allFiles = if isNil locFiles
                           then globFiles ++ concat pkgFiles
                           else locFiles
         -- Sort in reverse order of version number
         let sorted = sortBy (\x, y => compare (snd y) (snd x)) allFiles

         -- From what remains, pick the one with the highest version number.
         -- If there's none, report it
         -- (TODO: Can't do this quite yet due to idris2 build system...)
         case sorted of
              [] => if defs.options.session.ignoreMissingPkg
                       then pure ()
                       else throw (CantFindPackage (p ++ " (" ++ show bounds ++ ")"))
              ((p, _) :: ps) => addExtraDir p

dirOption : Dirs -> DirCommand -> Core ()
dirOption dirs LibDir
    = coreLift $ putStrLn
         (prefix_dir dirs </> "idris2-" ++ showVersion False version)

-- Options to be processed before type checking. Return whether to continue.
export
preOptions : {auto c : Ref Ctxt Defs} ->
             {auto o : Ref ROpts REPLOpts} ->
             List CLOpt -> Core Bool
preOptions [] = pure True
preOptions (NoBanner :: opts)
    = do setSession (record { nobanner = True } !getSession)
         preOptions opts
-- These things are processed later, but imply nobanner too
preOptions (OutputFile _ :: opts)
    = do setSession (record { nobanner = True } !getSession)
         preOptions opts
preOptions (ExecFn _ :: opts)
    = do setSession (record { nobanner = True } !getSession)
         preOptions opts
preOptions (IdeMode :: opts)
    = do setSession (record { nobanner = True } !getSession)
         preOptions opts
preOptions (IdeModeSocket _ :: opts)
    = do setSession (record { nobanner = True } !getSession)
         preOptions opts
preOptions (CheckOnly :: opts)
    = do setSession (record { nobanner = True } !getSession)
         preOptions opts
preOptions (Quiet :: opts)
    = do setOutput (REPL True)
         preOptions opts
preOptions (NoPrelude :: opts)
    = do setSession (record { noprelude = True } !getSession)
         preOptions opts
preOptions (SetCG e :: opts)
    = do defs <- get Ctxt
         case getCG (options defs) e of
            Just cg => do setCG cg
                          preOptions opts
            Nothing =>
              do coreLift $ putStrLn "No such code generator"
                 coreLift $ putStrLn $ "Code generators available: " ++
                                 showSep ", " (map fst (availableCGs (options defs)))
                 coreLift $ exitWith (ExitFailure 1)
preOptions (Directive d :: opts)
    = do setSession (record { directives $= (d::) } !getSession)
         preOptions opts
preOptions (PkgPath p :: opts)
    = do addPkgDir p anyBounds
         preOptions opts
preOptions (SourceDir d :: opts)
    = do setSourceDir (Just d)
         preOptions opts
preOptions (BuildDir d :: opts)
    = do setBuildDir d
         preOptions opts
preOptions (OutputDir d :: opts)
    = do setOutputDir (Just d)
         preOptions opts
preOptions (Directory d :: opts)
    = do defs <- get Ctxt
         dirOption (dirs (options defs)) d
         pure False
preOptions (Timing :: opts)
    = do setLogTimings True
         preOptions opts
preOptions (DebugElabCheck :: opts)
    = do setDebugElabCheck True
         preOptions opts
preOptions (RunREPL _ :: opts)
    = do setOutput (REPL True)
         setSession (record { nobanner = True } !getSession)
         preOptions opts
preOptions (FindIPKG :: opts)
    = do setSession (record { findipkg = True } !getSession)
         preOptions opts
preOptions (IgnoreMissingIPKG :: opts)
    = do setSession (record { ignoreMissingPkg = True } !getSession)
         preOptions opts
preOptions (DumpCases f :: opts)
    = do setSession (record { dumpcases = Just f } !getSession)
         preOptions opts
preOptions (DumpLifted f :: opts)
    = do setSession (record { dumplifted = Just f } !getSession)
         preOptions opts
preOptions (DumpANF f :: opts)
    = do setSession (record { dumpanf = Just f } !getSession)
         preOptions opts
preOptions (DumpVMCode f :: opts)
    = do setSession (record { dumpvmcode = Just f } !getSession)
         preOptions opts
preOptions (Logging n :: opts)
    = do setSession (record { logLevel $= insertLogLevel n } !getSession)
         preOptions opts
preOptions (ConsoleWidth n :: opts)
    = do setConsoleWidth n
         preOptions opts
preOptions (Color b :: opts)
    = do setColor b
         preOptions opts
preOptions (_ :: opts) = preOptions opts

-- Options to be processed after type checking. Returns whether execution
-- should continue (i.e., whether to start a REPL)
export
postOptions : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref MD Metadata} ->
              {auto o : Ref ROpts REPLOpts} ->
              REPLResult -> List CLOpt -> Core Bool
postOptions _ [] = pure True
postOptions res@(ErrorLoadingFile _ _) (OutputFile _ :: rest)
    = do ignore $ postOptions res rest
         pure False
postOptions res (OutputFile outfile :: rest)
    = do ignore $ compileExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN "main")) outfile
         ignore $ postOptions res rest
         pure False
postOptions res (ExecFn str :: rest)
    = do ignore $ execExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN str))
         ignore $ postOptions res rest
         pure False
postOptions res (CheckOnly :: rest)
    = do ignore $ postOptions res rest
         pure False
postOptions res (RunREPL str :: rest)
    = do replCmd str
         pure False
postOptions res (_ :: rest) = postOptions res rest

export
ideMode : List CLOpt -> Bool
ideMode [] = False
ideMode (IdeMode :: _) = True
ideMode (_ :: xs) = ideMode xs

export
ideModeSocket : List CLOpt -> Bool
ideModeSocket [] = False
ideModeSocket (IdeModeSocket _ :: _) = True
ideModeSocket (_ :: xs) = ideModeSocket xs
