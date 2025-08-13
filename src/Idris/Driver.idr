module Idris.Driver

import Compiler.Common

import Core.Binary
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.InitPrimitives
import Core.Metadata
import Core.Unify

import Idris.CommandLine
import Idris.Env
import Idris.IDEMode.REPL
import Idris.Package
import Idris.ProcessIdr
import Idris.REPL
import Idris.SetOptions
import Idris.Syntax
import Idris.Version
import Idris.Pretty
import Idris.Error

import IdrisPaths

import Data.List
import Data.String
import System
import System.Directory
import System.File.Meta
import System.File.Virtual
import Libraries.Utils.Path
import System.Term

import Yaffle.Main

%default covering

findInputs : List CLOpt -> Maybe (List1 String)
findInputs [] = Nothing
findInputs (InputFile f :: fs) =
  let rest = maybe [] toList (findInputs fs)
  in  Just (f ::: rest)
findInputs (_ :: fs) = findInputs fs

splitPaths : String -> List1 String
splitPaths = map trim . split (==pathSeparator)

-- Add extra data from the "IDRIS2_x" environment variables
updateEnv : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            Core ()
updateEnv
    = do defs <- get Ctxt
         noColor <- coreLift [ isJust noc || not tty | noc <- idrisGetEnv "NO_COLOR", tty <- isTTY stdout ]
         when noColor $ setColor False
         bprefix <- coreLift $ idrisGetEnv "IDRIS2_PREFIX"
         setPrefix (fromMaybe yprefix bprefix)
         bpath <- coreLift $ idrisGetEnv "IDRIS2_PATH"
         whenJust bpath $ traverseList1_ addExtraDir . splitPaths
         bdata <- coreLift $ idrisGetEnv "IDRIS2_DATA"
         whenJust bdata $ traverseList1_ addDataDir . splitPaths
         blibs <- coreLift $ idrisGetEnv "IDRIS2_LIBS"
         whenJust blibs $ traverseList1_ addLibDir . splitPaths
         pdirs <- coreLift $ idrisGetEnv "IDRIS2_PACKAGE_PATH"
         whenJust pdirs $ traverseList1_ addPackageSearchPath . splitPaths
         cg <- coreLift $ idrisGetEnv "IDRIS2_CG"
         whenJust cg $ \ e => case getCG (options defs) e of
           Just cg => setCG cg
           Nothing => throw (InternalError ("Unknown code generator " ++ show e))
         inccgs <- coreLift $ idrisGetEnv "IDRIS2_INC_CGS"
         whenJust inccgs $ \ cgs =>
           traverseList1_ (setIncrementalCG False) $
             map trim (split (==',') cgs)
         -- IDRIS2_PATH goes first so that it overrides this if there's
         -- any conflicts. In particular, that means that setting IDRIS2_PATH
         -- for the tests means they test the local version not the installed
         -- version
         defs <- get Ctxt
         -- add global package path to the package search paths (after those
         -- added by the user with IDRIS2_PACKAGE_PATH)
         addPackageSearchPath !pkgGlobalDirectory
         -- These might fail while bootstrapping
         catch (addPkgDir "prelude" anyBounds) (const (pure ()))
         catch (addPkgDir "base" anyBounds) (const (pure ()))
         addDataDir (prefix_dir (dirs (options defs)) </>
                        ("idris2-" ++ showVersion False version) </> "support")
         addLibDir (prefix_dir (dirs (options defs)) </>
                        ("idris2-" ++ showVersion False version) </> "lib")
         Just cwd <- coreLift $ currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         addLibDir cwd

updateREPLOpts : {auto o : Ref ROpts REPLOpts} ->
                 Core ()
updateREPLOpts
    = do ed <- coreLift $ idrisGetEnv "EDITOR"
         whenJust ed $ \ e => update ROpts { editor := e }

tryYaffle : List CLOpt -> Core Bool
tryYaffle [] = pure False
tryYaffle (Yaffle f :: _) = do yaffleMain f []
                               pure True
tryYaffle (c :: cs) = tryYaffle cs

ignoreMissingIpkg : List CLOpt -> Bool
ignoreMissingIpkg [] = False
ignoreMissingIpkg (IgnoreMissingIPKG :: _) = True
ignoreMissingIpkg (c :: cs) = ignoreMissingIpkg cs

tryTTM : List CLOpt -> Core Bool
tryTTM [] = pure False
tryTTM (Metadata f :: _) = do dumpTTM f
                              pure True
tryTTM (c :: cs) = tryTTM cs


banner : String
banner = #"""
       ____    __     _         ___
      /  _/___/ /____(_)____   |__ \
      / // __  / ___/ / ___/   __/ /     Version \#{ showVersion True version }
    _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org
   /___/\__,_/_/  /_/____/   /____/      Type :? for help

  Welcome to Idris 2.  Enjoy yourself!
  """#

checkVerbose : List CLOpt -> Bool
checkVerbose [] = False
checkVerbose (Verbose :: _) = True
checkVerbose (_ :: xs) = checkVerbose xs

stMain : List (String, Codegen) -> List CLOpt -> Core ()
stMain cgs opts
    = do False <- tryYaffle opts
            | True => pure ()
         False <- tryTTM opts
            | True => pure ()
         defs <- initDefs
         let updated = foldl (\o, (s, _) => addCG (s, Other s) o) (options defs) cgs
         c <- newRef Ctxt ({ options := updated } defs)
         s <- newRef Syn initSyntax
         setCG {c} $ maybe Chez (Other . fst) (head' cgs)
         addPrimitives

         setWorkingDir "."
         when (ignoreMissingIpkg opts) $
            setSession ({ ignoreMissingPkg := True } !getSession)

         let ide = ideMode opts
         let ideSocket = ideModeSocket opts
         let outmode = if ide then IDEMode 0 stdin stdout else REPL InfoLvl
         o <- newRef ROpts (REPL.Opts.defaultOpts Nothing outmode cgs)
         updateEnv
         fname <- case (findInputs opts) of
                       Just (fname ::: Nil) => pure $ Just fname
                       Nothing => pure Nothing
                       Just (fname1 ::: fnames) => do
                         let suggestion = nearMatchOptSuggestion fname1
                         renderedSuggestion <- maybe (pure "") render suggestion
                         quitWithError $
                           UserError """
                                     Expected at most one input file but was given: \{joinBy ", " (fname1 :: fnames)}
                                     \{renderedSuggestion}
                                     """
         update ROpts { mainfile := fname }

         -- start by going over the pre-options, and stop if we do not need to
         -- continue
         True <- preOptions opts
            | False => pure ()

         -- If there's a --build or --install, just do that then quit
         done <- flip catch quitWithError $ processPackageOpts opts

         when (not done) $ flip catch quitWithError $
            do when (checkVerbose opts) $ -- override Quiet if implicitly set
                   setOutput (REPL InfoLvl)
               u <- newRef UST initUState
               origin <- maybe
                 (pure $ Virtual Interactive) (\fname => do
                   modIdent <- ctxtPathToNS fname
                   pure (PhysicalIdrSrc modIdent)
                   ) fname
               m <- newRef MD (initMetadata origin)
               updateREPLOpts
               session <- getSession
               when (not $ nobanner session) $ do
                 iputStrLn $ pretty0 banner
                 when (isCons cgs) $ iputStrLn (reflow "With codegen for:" <++> hsep (pretty0 . fst <$> cgs))
               fname <- if findipkg session
                           then findIpkg fname
                           else pure fname
               setMainFile fname
               result <- case fname of
                    Nothing => logTime 1 "Loading prelude" $ do
                                 when (not $ noprelude session) $
                                   readPrelude True
                                 pure Done
                    Just f => logTime 1 "Loading main file" $ do
                                res <- loadMainFile f
                                displayStartupErrors res
                                pure res

               doRepl <- catch (postOptions result opts)
                               (\err => emitError err *> pure False)
               if doRepl then
                 if ide || ideSocket then
                   if not ideSocket
                    then do
                     setOutput (IDEMode 0 stdin stdout)
                     replIDE {c} {u} {m}
                   else do
                     let (host, port) = ideSocketModeAddress opts
                     f <- coreLift $ initIDESocketFile host port
                     case f of
                       Left err => do
                         coreLift $ putStrLn err
                         coreLift $ exitWith (ExitFailure 1)
                       Right file => do
                         setOutput (IDEMode 0 file file)
                         replIDE {c} {u} {m}
                 else do
                     repl {c} {u} {m}
                     showTimeRecord
                else
                    -- exit with an error code if there was an error, otherwise
                    -- just exit
                  do ropts <- get ROpts
                     showTimeRecord
                     whenJust (errorLine ropts) $ \ _ =>
                       coreLift $ exitWith (ExitFailure 1)

  where

  quitWithError : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                Error -> Core a
  quitWithError err = do
    doc <- display err
    msg <- render doc
    coreLift (die msg)

-- Run any options (such as --version or --help) which imply printing a
-- message then exiting. Returns wheter the program should continue

quitOpts : List CLOpt -> IO Bool
quitOpts [] = pure True
quitOpts (Version :: _)
    = do putStrLn versionMsg
         pure False
quitOpts (TTCVersion :: _)
    = do printLn ttcVersion
         pure False
quitOpts (Help Nothing :: _)
    = do putStrLn usage
         pure False
quitOpts (Help (Just HelpLogging) :: _)
    = do putStrLn helpTopics
         pure False
quitOpts (Help (Just HelpPragma) :: _)
    = do putStrLn pragmaTopics
         pure False
quitOpts (_ :: opts) = quitOpts opts

export
mainWithCodegens : List (String, Codegen) -> IO ()
mainWithCodegens cgs = do
  Right opts <- getCmdOpts
    | Left err => do ignore $ fPutStrLn stderr $ "Error: " ++ err
                     exitWith (ExitFailure 1)
  continue <- quitOpts opts
  when continue $ do
    setupTerm
    coreRun (stMain cgs opts)
      (\err : Error => do ignore $ fPutStrLn stderr $ "Uncaught error: " ++ show err
                          exitWith (ExitFailure 1))
      (\res => pure ())
