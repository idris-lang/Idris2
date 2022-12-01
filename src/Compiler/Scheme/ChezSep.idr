module Compiler.Scheme.ChezSep

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Generated
import Compiler.Scheme.Common
import Compiler.Scheme.Chez
import Compiler.Separate

import Core.Core
import Core.Hash
import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Options
import Core.TT
import Libraries.Utils.Path

import Data.List
import Data.List1
import Data.String

import Idris.Env
import Idris.Syntax

import System
import System.Directory
import System.Info

import Libraries.Data.Version
import Libraries.Utils.String

%default covering

schHeader : List String -> List String -> String
schHeader libs compilationUnits = """
  (import (chezscheme) (support)
      \{ unwords ["(" ++ cu ++ ")" | cu <- compilationUnits] })
  (case (machine-type)
    [(i3le ti3le a6le ta6le tarm64le) (load-shared-object "libc.so.6")]
    [(i3osx ti3osx a6osx ta6osx tarm64osx) (load-shared-object "libc.dylib")]
    [(i3nt ti3nt a6nt ta6nt) (load-shared-object "msvcrt.dll")]
    [else (load-shared-object "libc.so")]
  \{ unlines ["  (load-shared-object \"" ++ escapeStringChez lib ++ "\")" | lib <- libs] })

  """

schFooter : String
schFooter = """

  (collect 4)
  (blodwen-run-finalisers)
  """

startChez : String -> String -> String -> String
startChez chez appDirSh targetSh = Chez.startChezPreamble ++ """
  export LD_LIBRARY_PATH="$DIR/\{ appDirSh }:$LD_LIBRARY_PATH"
  export DYLD_LIBRARY_PATH="$DIR/\{ appDirSh }:$DYLD_LIBRARY_PATH"

  "\{ chez }" -q \
    --libdirs "$DIR/\{ appDirSh }" \
    --program "$DIR/\{ targetSh }" \
    "$@"
  """

startChezCmd : String -> String -> String -> String
startChezCmd chez appDirSh targetSh = """
  @echo off

  rem \{ generatedString "ChezSep" }

  set APPDIR=%~dp0
  set PATH=%APPDIR%\{ appDirSh };%PATH%

  "\{ chez }" -q \
    --libdirs "%APPDIR%\{ appDirSh }" \
    --program "%APPDIR%\{ targetSh }" \
    %*
  """

startChezWinSh : String -> String -> String -> String
startChezWinSh chez appDirSh targetSh = """
  #!/bin/sh
  # \{ generatedString "ChezSep" }

  set -e # exit on any error

  DIR=$(dirname "$(readlink -f -- "$0" || cygpath -a -- "$0")")
  PATH="$DIR/\{ appDirSh }:$PATH"

  "\{ chez }" --program "$DIR/\{ targetSh }" "$@"
  "\{ chez }" -q \
    --libdirs "$DIR/\{ appDirSh }" \
    --program "$DIR/\{ targetSh }" \
    "$@"
  """

-- TODO: parallelise this
compileChezLibraries : (chez : String) -> (libDir : String) -> (ssFiles : List String) -> Core ()
compileChezLibraries chez libDir ssFiles = coreLift_ $ system $ unwords
  [ "echo"
  , unwords
    [ "'(parameterize ([optimize-level 3] [compile-file-message #f]) (compile-library " ++ chezString ssFile ++ "))'"
      ++ " '(delete-file " ++ chezString ssFile ++ ")'"
      -- we must delete the SS file to prevent it from interfering with the SO files
      -- we keep the .hash file, though, so we still keep track of what to rebuild
    | ssFile <- ssFiles
    ]
  , "|", chez, "-q", "--libdirs", libDir
  ]

compileChezLibrary : (chez : String) -> (libDir : String) -> (ssFile : String) -> Core ()
compileChezLibrary chez libDir ssFile = coreLift_ $ system $ unwords
  [ "echo"
  , "'(parameterize ([optimize-level 3] [compile-file-message #f]) (compile-library " ++ chezString ssFile ++ "))'"
  , "'(delete-file " ++ chezString ssFile ++ ")'"
  , "|", chez, "-q", "--libdirs", libDir
  ]

compileChezProgram : (chez : String) -> (libDir : String) -> (ssFile : String) -> Core ()
compileChezProgram chez libDir ssFile = coreLift_ $ system $ unwords
  [ "echo"
  , "'(parameterize ([optimize-level 3] [compile-file-message #f]) (compile-program " ++ chezString ssFile ++ "))'"
  , "'(delete-file " ++ chezString ssFile ++ ")'"
  , "|", chez, "-q", "--libdirs", libDir
  ]

chezNS : Namespace -> String
chezNS ns = case showNSWithSep "-" ns of
  "" => "unqualified"
  nss => nss

-- arbitrarily name the compilation unit
-- after the alphabetically first namespace contained within
chezLibraryName : CompilationUnit def -> String
chezLibraryName cu = chezNS (min1 cu.namespaces)
  where
    -- the stdlib of the previous stable version
    -- has some strange version of List1.foldl1
    -- so we reimplement it here for compatibility
    min1 : List1 Namespace -> Namespace
    min1 (ns ::: nss) = foldl min ns nss

touch : String -> Core ()
touch s = coreLift_ $ system ["touch", s]

record ChezLib where
  constructor MkChezLib
  name : String
  isOutdated : Bool  -- needs recompiling

||| Compile a TT expression to a bunch of Chez Scheme files
compileToSS : Ref Ctxt Defs -> String -> String -> ClosedTerm -> Core (Bool, List ChezLib)
compileToSS c chez appdir tm = do
  -- process native libraries
  ds <- getDirectives Chez
  libs <- findLibs ds
  traverse_ copyLib libs
  version <- coreLift $ chezVersion chez

  -- get the material for compilation
  cdata <- getCompileData False Cases tm
  let ctm = forget (mainExpr cdata)
  let ndefs = namedDefs cdata
  let cui = getCompilationUnits ndefs

  -- copy the support library
  support <- readDataFile "chez/support-sep.ss"
  let supportHash = show $ hash support
  supportChanged <-
    coreLift (readFile (appdir </> "support.hash")) >>= \case
      Left err => pure True
      Right fileHash => pure (fileHash /= supportHash)
  when supportChanged $ do
    Core.writeFile (appdir </> "support.ss") support
    Core.writeFile (appdir </> "support.hash") supportHash

  -- TODO: add extraRuntime
  -- the problem with this is that it's unclear what to put in the (export) clause of the library
  -- extraRuntime <- getExtraRuntime ds

  -- for each compilation unit, generate code
  chezLibs <- for cui.compilationUnits $ \cu => do
    let chezLib = chezLibraryName cu

    -- check if the hash has changed
    -- TODO: also check that the .so file exists
    let cuHash = show (hash cu)
    hashChanged <-
      coreLift (readFile (appdir </> chezLib <.> "hash")) >>= \case
        Left err       => pure True
        Right fileHash => pure (fileHash /= cuHash)

    -- generate code only when necessary
    when hashChanged $ do
      defs <- get Ctxt
      l <- newRef {t = List String} Loaded ["libc", "libc 6"]
      s <- newRef {t = List String} Structs []

      -- create imports + exports + header + footer
      let imports = unwords
            [ "(" ++
                maybe
                  "unqualified"
                  chezLibraryName
                  (SortedMap.lookup cuid cui.byId)
              ++ ")"
            | cuid <- SortedSet.toList cu.dependencies
            ]
      let exports = unwords $ concat
            -- constructors don't generate Scheme definitions
            [ case d of
                MkNmCon _ _ _ => []
                _ => [schName dn]
            | (dn, fc, d) <- cu.definitions
            ]
      let header =
            "(library (" ++ chezLib ++ ")\n"
            ++ "  (export " ++ exports ++ ")\n"
            ++ "  (import (chezscheme) (support) " ++ imports ++ ")\n\n"
      let footer = ")"

      fgndefs <- traverse (Chez.getFgnCall version) cu.definitions
      compdefs <- traverse (getScheme Chez.chezExtPrim Chez.chezString) cu.definitions
      loadlibs <- traverse (loadLib appdir) (mapMaybe fst fgndefs)

      -- write the files
      log "compiler.scheme.chez" 3 $ "Generating code for " ++ chezLib
      Core.writeFile (appdir </> chezLib <.> "ss") $ fastConcat $
        [header]
        ++ map snd fgndefs  -- definitions using foreign libs
        ++ compdefs
        ++ loadlibs  -- foreign library load statements
        ++ [footer]

      Core.writeFile (appdir </> chezLib <.> "hash") cuHash

    pure (MkChezLib chezLib hashChanged)

  -- main module
  main <- schExp Chez.chezExtPrim Chez.chezString 0 ctm
  Core.writeFile (appdir </> "mainprog.ss") $ unlines $
    [ schHeader (map snd libs) [lib.name | lib <- chezLibs]
    , "(collect-request-handler (lambda () (collect) (blodwen-run-finalisers)))"
    , main
    , schFooter
    ]

  pure (supportChanged, chezLibs)

makeSh : String -> String -> String -> String -> Core ()
makeSh chez outShRel appDirSh targetSh =
  Core.writeFile outShRel (startChez chez appDirSh targetSh)

||| Make Windows start scripts, one for bash environments and one batch file
makeShWindows : String -> String -> String -> String -> Core ()
makeShWindows chez outShRel appDirSh targetSh = do
  let cmdFile = outShRel ++ ".cmd"
  Core.writeFile cmdFile (startChezCmd chez appDirSh targetSh)
  Core.writeFile outShRel (startChezWinSh chez appDirSh targetSh)

||| Chez Scheme implementation of the `compileExpr` interface.
compileExpr :
  Bool ->
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr makeitso c s tmpDir outputDir tm outfile = do
  -- set up paths
  Just cwd <- coreLift currentDir
       | Nothing => throw (InternalError "Can't get current directory")
  let appDirSh  = outfile ++ "_app"  -- relative to the launcher shell script
  let appDirRel = outputDir </> appDirSh  -- relative to CWD
  let appDirAbs = cwd </> appDirRel
  coreLift_ $ mkdirAll appDirRel

  -- generate the code
  chez <- coreLift $ findChez
  (supportChanged, chezLibs) <- compileToSS c chez appDirRel tm

  -- compile the code
  logTime 2 "Make SO" $ when makeitso $ do
    -- compile the support code
    when supportChanged $ do
      log "compiler.scheme.chez" 3 $ "Compiling support"
      compileChezLibrary chez appDirRel (appDirRel </> "support.ss")

    -- compile every compilation unit
    compileChezLibraries chez appDirRel
      [appDirRel </> lib.name <.> "ss" | lib <- chezLibs, lib.isOutdated]

    -- touch them in the right order to make the timestamps right
    -- even for the libraries that were not recompiled
    for_ chezLibs $ \lib => do
      log "compiler.scheme.chez" 3 $ "Touching " ++ lib.name
      touch (appDirRel </> lib.name <.> "so")

    -- compile the main program
    compileChezProgram chez appDirRel (appDirRel </> "mainprog.ss")

  -- generate the launch script
  let outShRel = outputDir </> outfile
  let launchTargetSh = appDirSh </> "mainprog" <.> (if makeitso then "so" else "ss")
  if isWindows
     then makeShWindows chez outShRel appDirSh launchTargetSh
     else makeSh        chez outShRel appDirSh launchTargetSh
  coreLift_ $ chmodRaw outShRel 0o755
  pure (Just outShRel)

||| Chez Scheme implementation of the `executeExpr` interface.
||| This implementation simply runs the usual compiler, saving it to a temp file, then interpreting it.
executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm
    = do Just sh <- compileExpr False c s tmpDir tmpDir tm "_tmpchez"
            | Nothing => throw (InternalError "compileExpr returned Nothing")
         coreLift_ $ system [sh]

||| Codegen wrapper for Chez scheme implementation.
export
codegenChezSep : Codegen
codegenChezSep = MkCG (compileExpr True) executeExpr Nothing Nothing
