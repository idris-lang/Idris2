module Idris.SetOptions

import Core.Context
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Unify
import Libraries.Utils.Path
import Libraries.Data.List.Extra
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

||| Dissected information about a package directory
record PkgDir where
  constructor MkPkgDir
  ||| Directory name. Example "contrib-0.3.0"
  dirName : String
  ||| Package name. Example "contrib"
  pkgName : String
  ||| Package version. Example `Just $ MkPkgVersion (0 ::: [3,0])`
  version : Maybe PkgVersion

-- dissects a directory name, trying to extract
-- the corresponding package name and -version
pkgDir : String -> PkgDir
pkgDir str =
   -- Split the dir name into parts concatenated by "-"
   -- treating the last part as the version number
   -- and the initial parts as the package name.
   -- For reasons of backwards compatibility, we also
   -- accept hyphenated directory names without a part
   -- corresponding to a version number.
   case Lib.unsnoc $ split (== '-') str of
     (Nil, last) => MkPkgDir str last Nothing
     (init,last) =>
       case toVersion last of
         Just v  => MkPkgDir str (concat $ intersperse "-" init) (Just v)
         Nothing => MkPkgDir str str Nothing
  where
    toVersion : String -> Maybe PkgVersion
    toVersion = map MkPkgVersion
              . traverse parsePositive
              . split (== '.')

dirEntries : String -> IO (List String)
dirEntries dname =
    do Right d <- openDir dname
         | Left err => pure []
       getFiles d []
  where
    getFiles : Directory -> List String -> IO (List String)
    getFiles d acc
        = do Right str <- dirEntry d
               | Left err => pure (reverse acc)
             getFiles d (str :: acc)

getPackageDirs : String -> IO (List PkgDir)
getPackageDirs dname = map pkgDir <$> dirEntries dname

-- Get a list of all the candidate directories that match a package spec
-- in a given path. Return an empty list on file error (e.g. path not existing)
export
candidateDirs : String -> String -> PkgVersionBounds ->
                IO (List (String, Maybe PkgVersion))
candidateDirs dname pkg bounds =
  mapMaybe checkBounds <$> getPackageDirs dname

  where checkBounds : PkgDir -> Maybe (String,Maybe PkgVersion)
        checkBounds (MkPkgDir dirName pkgName ver) =
          do guard (pkgName == pkg && inBounds ver bounds)
             pure ((dname </> dirName), ver)

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

--------------------------------------------------------------------------------
--          Bash Autocompletions
--------------------------------------------------------------------------------

findIpkg : {auto c : Ref Ctxt Defs} -> Core (List String)
findIpkg =
  do Just srcdir <- coreLift currentDir
       | Nothing => throw (InternalError "Can't get current directory")
     fs <- coreLift $ dirEntries srcdir
     pure $ filter (".ipkg" `isSuffixOf`) fs

packageNames : String -> IO (List String)
packageNames dir = filter notHidden . map pkgName <$> getPackageDirs dir
  where notHidden : String -> Bool
        notHidden = not . isPrefixOf "."


findPackages : {auto c : Ref Ctxt Defs} -> Core (List String)
findPackages =
  do defs <- get Ctxt
     let globaldir = prefix_dir (dirs (options defs)) </>
                           "idris2-" ++ showVersion False version
     let depends = depends_dir (dirs (options defs))
     Just srcdir <- coreLift currentDir
         | Nothing => throw (InternalError "Can't get current directory")
     let localdir = srcdir </> depends

     -- Get candidate directories from the global install location,
     -- and the local package directory
     locFiles <- coreLift $ packageNames localdir
     globFiles <- coreLift $ packageNames globaldir
     pure $ locFiles ++ globFiles

-- keep only those Strings, of which `x` is a prefix
prefixOnly : String -> List String -> List String
prefixOnly x = sortedNub . filter (\s => x /= s && isPrefixOf x s)

-- filter a list of Strings by the given prefix, but only if
-- the prefix is not "--", bash complete's constant for empty input.
prefixOnlyIfNonEmpty : String -> List String -> List String
prefixOnlyIfNonEmpty "--" = id
prefixOnlyIfNonEmpty s    = prefixOnly s


-- list of registered codegens
codegens : {auto c : Ref Ctxt Defs} -> Core (List String)
codegens = map fst . availableCGs . options <$> get Ctxt

logLevels : List String
logLevels = map fst knownTopics >>= prefixes . forget . split (== '.')
  where prefixes : List String -> List String
        prefixes [] = []
        prefixes (x :: xs) = x :: map (x ++ "." ++) (prefixes xs)

-- given a pair of strings, the first representing the word
-- actually being edited, the second representing the word
-- before the one being edited, return a list of possible
-- completions. If the list of completions is empty, bash
-- will perform directory completion.
opts : {auto c : Ref Ctxt Defs} -> String -> String -> Core (List String)
opts "--" "idris2"  = pure optionFlags

-- codegens
opts x "--cg"      = prefixOnlyIfNonEmpty x <$> codegens
opts x "--codegen" = prefixOnlyIfNonEmpty x <$> codegens

-- packages
opts x "-p"        = prefixOnlyIfNonEmpty x <$> findPackages
opts x "--package" = prefixOnlyIfNonEmpty x <$> findPackages

-- logging
opts x "--log"     = pure $ prefixOnlyIfNonEmpty x logLevels

-- with directories
opts "--" "-o"           = pure []
opts "--" "--output"     = pure []
opts "--" "--source-dir" = pure []
opts "--" "--build-dir"  = pure []
opts "--" "--output-dir" = pure []

-- with package files
opts x "--build"     = prefixOnlyIfNonEmpty x <$> findIpkg
opts x "--install"   = prefixOnlyIfNonEmpty x <$> findIpkg
opts x "--mkdoc"     = prefixOnlyIfNonEmpty x <$> findIpkg
opts x "--typecheck" = prefixOnlyIfNonEmpty x <$> findIpkg
opts x "--clean"     = prefixOnlyIfNonEmpty x <$> findIpkg
opts x "--repl"      = prefixOnlyIfNonEmpty x <$> findIpkg

-- options
opts x _ = pure $ if (x `elem` optionFlags)
                     -- `x` is already a known option => perform
                     -- directory completion
                     then Nil
                     else prefixOnly x optionFlags

-- bash autocompletion script using the given function name
completionScript : (fun : String) -> String
completionScript fun =
  let fun' = "_" ++ fun
   in unlines [ fun' ++ "()"
              , "{"
              , "  ED=$([ -z $2 ] && echo \"--\" || echo $2)"
              , "  COMPREPLY=($(idris2 --bash-completion $ED $3))"
              , "}"
              , ""
              , "complete -F " ++ fun' ++ " -o dirnames idris2"
              ]

--------------------------------------------------------------------------------
--          Processing Options
--------------------------------------------------------------------------------

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
preOptions (Profile :: opts)
    = do setSession (record { profile = True } !getSession)
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
    = do setSession (record { logEnabled = True,
                              logLevel $= insertLogLevel n } !getSession)
         preOptions opts
preOptions (ConsoleWidth n :: opts)
    = do setConsoleWidth n
         preOptions opts
preOptions (Color b :: opts)
    = do setColor b
         preOptions opts
preOptions (WarningsAsErrors :: opts)
    = do setSession (record { warningsAsErrors = True } !getSession)
         preOptions opts
preOptions (IgnoreShadowingWarnings :: opts)
    = do setSession (record { showShadowingWarning = False } !getSession)
         preOptions opts
preOptions (BashCompletion a b :: _)
    = do os <- opts a b
         coreLift $ putStr $ unlines os
         pure False
preOptions (BashCompletionScript fun :: _)
    = do coreLift $ putStrLn $ completionScript fun
         pure False
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
