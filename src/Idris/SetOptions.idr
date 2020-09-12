module Idris.SetOptions

import Core.Context
import Core.Directory
import Core.Metadata
import Core.Options
import Core.Unify
import Utils.Path

import Idris.CommandLine
import Idris.Error
import Idris.REPL
import Idris.Syntax
import Idris.Version

import IdrisPaths

import Data.So
import System

%default covering

-- TODO: Version numbers on dependencies
export
addPkgDir : {auto c : Ref Ctxt Defs} ->
            String -> Core ()
addPkgDir p
    = do defs <- get Ctxt
         addExtraDir (prefix_dir (dirs (options defs)) </>
                             "idris2-" ++ showVersion False version </> p)

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
    = do addPkgDir p
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
    = do postOptions res rest
         pure False
postOptions res (OutputFile outfile :: rest)
    = do compileExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN "main")) outfile
         postOptions res rest
         pure False
postOptions res (ExecFn str :: rest)
    = catch (do execExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN str))
                postOptions res rest
                pure False)
            (\err => do perror err >>= printError; pure False)
postOptions res (CheckOnly :: rest)
    = do postOptions res rest
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
