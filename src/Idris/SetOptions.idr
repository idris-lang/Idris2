module Idris.SetOptions

import Compiler.Common

import Core.Context
import Core.Metadata
import Core.Options
import Core.Unify
import Libraries.Utils.Path
import Libraries.Data.List.Extra

import Idris.CommandLine
import Idris.Package.Types
import Idris.Pretty
import Idris.ProcessIdr
import Idris.REPL
import Idris.Syntax
import Idris.Version

import Data.List
import Data.List1
import Data.String

import Libraries.Data.List1 as Lib

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

getPackageDirs : String -> IO (List PkgDir)
getPackageDirs dname = map pkgDir . either (const []) id <$> listDir dname

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

globalPackageDir : {auto c : Ref Ctxt Defs} -> Core String
globalPackageDir
    = do defs <- get Ctxt
         pure $ prefix_dir (dirs (options defs)) </>
                  "idris2-" ++ showVersion False version

localPackageDir : {auto c : Ref Ctxt Defs} -> Core String
localPackageDir
    = do defs <- get Ctxt
         Just srcdir <- coreLift currentDir
             | Nothing => throw (InternalError "Can't get current directory")
         let depends = depends_dir (dirs (options defs))
         pure $ srcdir </> depends

||| Find all package directories (plus version) matching
||| the given package name and version bounds. Results
||| will be sorted with the latest package version first.
export
findPkgDirs :
    Ref Ctxt Defs =>
    String ->
    PkgVersionBounds ->
    Core (List (String, Maybe PkgVersion))
findPkgDirs p bounds = do
  defs <- get Ctxt
  globaldir <- globalPackageDir
  localdir <- localPackageDir

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
  pure $ sortBy (\x, y => compare (snd y) (snd x)) allFiles

export
findPkgDir :
    Ref Ctxt Defs =>
    String ->
    PkgVersionBounds ->
    Core (Maybe String)
findPkgDir p bounds = do
  defs <- get Ctxt
  [] <- findPkgDirs p bounds | ((p,_) :: _) => pure (Just p)

  -- From what remains, pick the one with the highest version number.
  -- If there's none, report it
  -- (TODO: Can't do this quite yet due to idris2 build system...)
  if defs.options.session.ignoreMissingPkg
     then pure Nothing
     else throw (CantFindPackage (p ++ " (" ++ show bounds ++ ")"))

export
addPkgDir : {auto c : Ref Ctxt Defs} ->
            String -> PkgVersionBounds -> Core ()
addPkgDir p bounds = do
    Just p <- findPkgDir p bounds
        | Nothing => pure ()
    addExtraDir p

visiblePackages : String -> IO (List PkgDir)
visiblePackages dir = filter viable <$> getPackageDirs dir
  where notHidden : PkgDir -> Bool
        notHidden = not . isPrefixOf "." . pkgName

        notDenylisted : PkgDir -> Bool
        notDenylisted = not . flip elem (the (List String) ["include", "lib", "support", "refc"]) . pkgName

        viable : PkgDir -> Bool
        viable p = notHidden p && notDenylisted p

findPackages : {auto c : Ref Ctxt Defs} -> Core (List PkgDir)
findPackages
    = do -- global packages
         defs <- get Ctxt
         globalPkgs <- coreLift $ visiblePackages !globalPackageDir
         -- additional packages in directories specified
         let pkgDirs = (options defs).dirs.package_dirs
         additionalPkgs <- coreLift $ traverse (\d => visiblePackages d) pkgDirs
         -- local packages
         localPkgs <- coreLift $ visiblePackages !localPackageDir
         pure $ globalPkgs ++ (join additionalPkgs) ++ localPkgs

listPackages : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               Core ()
listPackages
    = do pkgs <- sortBy (compare `on` pkgName) <$> findPackages
         traverse_ (iputStrLn . pkgDesc) pkgs
  where
    pkgDesc : PkgDir -> Doc IdrisAnn
    pkgDesc (MkPkgDir _ pkgName version) = pretty0 pkgName <++> parens (byShow version)

dirOption : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            Dirs -> DirCommand -> Core ()
dirOption dirs LibDir
    = coreLift $ putStrLn
         (prefix_dir dirs </> "idris2-" ++ showVersion False version)
dirOption dirs BlodwenPaths
    = iputStrLn $ pretty0 (toString dirs)
dirOption dirs Prefix
    = coreLift $ putStrLn (prefix_dir dirs)

--------------------------------------------------------------------------------
--          Bash Autocompletions
--------------------------------------------------------------------------------

findIpkg : {auto c : Ref Ctxt Defs} -> Core (List String)
findIpkg =
  do Just srcdir <- coreLift currentDir
       | Nothing => throw (InternalError "Can't get current directory")
     Right fs <- coreLift $ listDir srcdir
       | Left err => pure []
     pure $ filter (".ipkg" `isSuffixOf`) fs

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
opts x "-p"        = prefixOnlyIfNonEmpty x . (map pkgName) <$> findPackages
opts x "--package" = prefixOnlyIfNonEmpty x . (map pkgName) <$> findPackages

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
completionScript fun = let fun' = "_" ++ fun in """
  \{ fun' }()
  {
    ED=$([ -z $2 ] && echo "--" || echo $2)
    COMPREPLY=($(idris2 --bash-completion $ED $3))
  }

  complete -F \{ fun' } -o default idris2
  """

--------------------------------------------------------------------------------
--          Processing Options
--------------------------------------------------------------------------------

export
setIncrementalCG : {auto c : Ref Ctxt Defs} ->
                   {auto o : Ref ROpts REPLOpts} ->
                   Bool -> String -> Core ()
setIncrementalCG failOnError cgn
    = do defs <- get Ctxt
         case getCG (options defs) cgn of
           Just cg =>
               do Just cgd <- getCG cg
                       | Nothing => pure ()
                  let Just _ = incCompileFile cgd
                       | Nothing =>
                            if failOnError
                               then do coreLift $ putStrLn $ cgn ++ " does not support incremental builds"
                                       coreLift $ exitWith (ExitFailure 1)
                               else pure ()
                  setSession ({ incrementalCGs $= (cg :: )} !getSession)
           Nothing =>
              if failOnError
                 then do coreLift $ putStrLn "No such code generator"
                         coreLift $ putStrLn $ "Code generators available: " ++
                                         showSep ", " (map fst (availableCGs (options defs)))
                         coreLift $ exitWith (ExitFailure 1)
                 else pure ()

||| Options to be processed before type checking. Return whether to continue.
export
preOptions : {auto c : Ref Ctxt Defs} ->
             {auto o : Ref ROpts REPLOpts} ->
             List CLOpt -> Core Bool
preOptions [] = pure True
preOptions (NoBanner :: opts)
    = do setSession ({ nobanner := True } !getSession)
         preOptions opts
-- These things are processed later, but imply nobanner too
preOptions (OutputFile _ :: opts)
    = do setSession ({ nobanner := True } !getSession)
         preOptions opts
preOptions (ExecFn _ :: opts)
    = do setSession ({ nobanner := True } !getSession)
         preOptions opts
preOptions (IdeMode :: opts)
    = do setSession ({ nobanner := True } !getSession)
         preOptions opts
preOptions (IdeModeSocket _ :: opts)
    = do setSession ({ nobanner := True } !getSession)
         preOptions opts
preOptions (CheckOnly :: opts)
    = do setSession ({ nobanner := True } !getSession)
         preOptions opts
preOptions (Profile :: opts)
    = do setSession ({ profile := True } !getSession)
         preOptions opts
preOptions (Quiet :: opts)
    = do setOutput (REPL VerbosityLvl.ErrorLvl)
         preOptions opts
preOptions (NoPrelude :: opts)
    = do setSession ({ noprelude := True } !getSession)
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
    = do setSession ({ directives $= (d::) } !getSession)
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
preOptions (ListPackages :: opts)
    = do listPackages
         pure False
preOptions (Timing tm :: opts)
    = do setLogTimings (fromMaybe 10 tm)
         preOptions opts
preOptions (DebugElabCheck :: opts)
    = do setDebugElabCheck True
         preOptions opts
preOptions (AltErrorCount c :: opts)
    = do setSession ({ logErrorCount := c } !getSession)
         preOptions opts
preOptions (RunREPL _ :: opts)
    = do setOutput (REPL VerbosityLvl.ErrorLvl)
         setSession ({ nobanner := True } !getSession)
         preOptions opts
preOptions (FindIPKG :: opts)
    = do setSession ({ findipkg := True } !getSession)
         preOptions opts
preOptions (IgnoreMissingIPKG :: opts)
    = do setSession ({ ignoreMissingPkg := True } !getSession)
         preOptions opts
preOptions (DumpCases f :: opts)
    = do setSession ({ dumpcases := Just f } !getSession)
         preOptions opts
preOptions (DumpLifted f :: opts)
    = do setSession ({ dumplifted := Just f } !getSession)
         preOptions opts
preOptions (DumpANF f :: opts)
    = do setSession ({ dumpanf := Just f } !getSession)
         preOptions opts
preOptions (DumpVMCode f :: opts)
    = do setSession ({ dumpvmcode := Just f } !getSession)
         preOptions opts
preOptions (Logging n :: opts)
    = do setSession ({ logEnabled := True,
                       logLevel $= insertLogLevel n } !getSession)
         preOptions opts
preOptions (ConsoleWidth n :: opts)
    = do setConsoleWidth n
         preOptions opts
preOptions (ShowMachineNames :: opts)
    = do pp <- getPPrint
         setPPrint ({ showMachineNames := True } pp)
         preOptions opts
preOptions (ShowNamespaces :: opts)
    = do pp <- getPPrint
         setPPrint ({ fullNamespace := True } pp)
         preOptions opts
preOptions (Color b :: opts)
    = do setColor b
         preOptions opts
preOptions (WarningsAsErrors :: opts)
    = do updateSession ({ warningsAsErrors := True })
         preOptions opts
preOptions (IgnoreShadowingWarnings :: opts)
    = do updateSession ({ showShadowingWarning := False })
         preOptions opts
preOptions (HashesInsteadOfModTime :: opts)
    = do throw (InternalError "-Xcheck-hashes disabled (see issue #1935)")
         updateSession ({ checkHashesInsteadOfModTime := True })
         preOptions opts
preOptions (CaseTreeHeuristics :: opts)
    = do updateSession ({ caseTreeHeuristics := True })
         preOptions opts
preOptions (IncrementalCG e :: opts)
    = do defs <- get Ctxt
         setIncrementalCG True e
         preOptions opts
preOptions (WholeProgram :: opts)
    = do updateSession ({ wholeProgram := True })
         preOptions opts
preOptions (BashCompletion a b :: _)
    = do os <- opts a b
         coreLift $ putStr $ unlines os
         pure False
preOptions (BashCompletionScript fun :: _)
    = do coreLift $ putStrLn $ completionScript fun
         pure False
preOptions (Total :: opts)
    = do updateSession ({ totalReq := Total })
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
    = do ignore $ compileExp (PRef EmptyFC (UN $ Basic "main")) outfile
         ignore $ postOptions res rest
         pure False
postOptions res (ExecFn str :: rest)
    = do ignore $ execExp (PRef EmptyFC (UN $ Basic str))
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
