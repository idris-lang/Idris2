module Idris.Driver

import Compiler.Common

import Core.Context.Log
import Core.Core
import Core.InitPrimitives
import Core.Metadata
import Core.Unify

import Idris.CommandLine
import Idris.Env
import Idris.IDEMode.REPL
import Idris.ModTree
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
import Data.List1
import Data.So
import Data.Strings
import System
import System.Directory
import System.File
import Libraries.Utils.Path
import Libraries.Utils.Term

import Yaffle.Main

%default covering

findInput : List CLOpt -> Maybe String
findInput [] = Nothing
findInput (InputFile f :: fs) = Just f
findInput (_ :: fs) = findInput fs

-- Add extra data from the "IDRIS2_x" environment variables
updateEnv : {auto c : Ref Ctxt Defs} ->
            Core ()
updateEnv
    = do defs <- get Ctxt
         bprefix <- coreLift $ idrisGetEnv "IDRIS2_PREFIX"
         the (Core ()) $ case bprefix of
              Just p => setPrefix p
              Nothing => setPrefix yprefix
         bpath <- coreLift $ idrisGetEnv "IDRIS2_PATH"
         the (Core ()) $ case bpath of
              Just path => do traverseList1_ addExtraDir (map trim (split (==pathSeparator) path))
              Nothing => pure ()
         bdata <- coreLift $ idrisGetEnv "IDRIS2_DATA"
         the (Core ()) $ case bdata of
              Just path => do traverseList1_ addDataDir (map trim (split (==pathSeparator) path))
              Nothing => pure ()
         blibs <- coreLift $ idrisGetEnv "IDRIS2_LIBS"
         the (Core ()) $ case blibs of
              Just path => do traverseList1_ addLibDir (map trim (split (==pathSeparator) path))
              Nothing => pure ()
         pdirs <- coreLift $ idrisGetEnv "IDRIS2_PACKAGE_PATH"
         the (Core ()) $ case pdirs of
              Just path => do traverseList1_ addPackageDir (map trim (split (==pathSeparator) path))
              Nothing => pure ()
         cg <- coreLift $ idrisGetEnv "IDRIS2_CG"
         the (Core ()) $ case cg of
              Just e => case getCG (options defs) e of
                             Just cg => setCG cg
                             Nothing => throw (InternalError ("Unknown code generator " ++ show e))
              Nothing => pure ()

         -- IDRIS2_PATH goes first so that it overrides this if there's
         -- any conflicts. In particular, that means that setting IDRIS2_PATH
         -- for the tests means they test the local version not the installed
         -- version
         defs <- get Ctxt
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
    = do opts <- get ROpts
         ed <- coreLift $ idrisGetEnv "EDITOR"
         the (Core ()) $ case ed of
              Just e => put ROpts (record { editor = e } opts)
              Nothing => pure ()

showInfo : {auto c : Ref Ctxt Defs}
        -> {auto o : Ref ROpts REPLOpts}
        -> List CLOpt
        -> Core Bool
showInfo Nil = pure False
showInfo (BlodwenPaths :: _)
    = do defs <- get Ctxt
         iputStrLn $ pretty (toString (dirs (options defs)))
         pure True
showInfo (_::rest) = showInfo rest

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
banner = "     ____    __     _         ___                                           \n" ++
         "    /  _/___/ /____(_)____   |__ \\                                          \n" ++
         "    / // __  / ___/ / ___/   __/ /     Version " ++ showVersion True version ++ "\n" ++
         "  _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org           \n" ++
         " /___/\\__,_/_/  /_/____/   /____/      Type :? for help                     \n" ++
         "\n" ++
         "Welcome to Idris 2.  Enjoy yourself!"

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
         c <- newRef Ctxt (record { options = updated } defs)
         s <- newRef Syn initSyntax
         setCG {c} $ maybe Chez (Other . fst) (head' cgs)
         addPrimitives

         setWorkingDir "."
         when (ignoreMissingIpkg opts) $
            setSession (record { ignoreMissingPkg = True } !getSession)

         updateEnv
         let ide = ideMode opts
         let ideSocket = ideModeSocket opts
         let outmode = if ide then IDEMode 0 stdin stdout else REPL False
         let fname = findInput opts
         o <- newRef ROpts (REPL.Opts.defaultOpts fname outmode cgs)

         finish <- showInfo opts
         when (not finish) $ do
           -- If there's a --build or --install, just do that then quit
           done <- processPackageOpts opts

           when (not done) $ flip catch renderError $
              do True <- preOptions opts
                     | False => pure ()

                 when (checkVerbose opts) $ -- override Quiet if implicitly set
                     setOutput (REPL False)
                 u <- newRef UST initUState
                 m <- newRef MD initMetadata
                 updateREPLOpts
                 session <- getSession
                 when (not $ nobanner session) $ do
                   iputStrLn $ pretty banner
                   when (isCons cgs) $ iputStrLn (reflow "With codegen for:" <++> hsep (pretty . fst <$> cgs))
                 fname <- if findipkg session
                             then findIpkg fname
                             else pure fname
                 setMainFile fname
                 result <- case fname of
                      Nothing => logTime "+ Loading prelude" $ do
                                   when (not $ noprelude session) $
                                     readPrelude True
                                   pure Done
                      Just f => logTime "+ Loading main file" $ do
                                  res <- loadMainFile f
                                  displayErrors res
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
                       case errorLine ropts of
                         Nothing => pure ()
                         Just _ => coreLift $ exitWith (ExitFailure 1)

  where

  renderError : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto o : Ref ROpts REPLOpts} ->
                Error -> Core ()
  renderError err = do
    doc <- perror err
    msg <- render doc
    throw (UserError msg)

-- Run any options (such as --version or --help) which imply printing a
-- message then exiting. Returns wheter the program should continue

quitOpts : List CLOpt -> IO Bool
quitOpts [] = pure True
quitOpts (Version :: _)
    = do putStrLn versionMsg
         pure False
quitOpts (Help :: _)
    = do putStrLn usage
         pure False
quitOpts (ShowPrefix :: _)
    = do putStrLn yprefix
         pure False
quitOpts (_ :: opts) = quitOpts opts

export
mainWithCodegens : List (String, Codegen) -> IO ()
mainWithCodegens cgs = do
  Right opts <- getCmdOpts
    | Left err => do putStrLn err
                     putStrLn usage
  continue <- quitOpts opts
  when continue $ do
    setupTerm
    coreRun (stMain cgs opts)
      (\err : Error => do putStrLn ("Uncaught error: " ++ show err)
                          exitWith (ExitFailure 1))
      (\res => pure ())
