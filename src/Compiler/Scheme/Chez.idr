module Compiler.Scheme.Chez

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Generated
import Compiler.Opts.ToplevelConstants
import Compiler.Scheme.Common

import Core.Directory
import Protocol.Hex

import Idris.Env
import Idris.Syntax

import Data.Maybe
import Data.SortedSet
import Data.String

import System
import System.Directory
import System.Info

import Libraries.Data.Version
import Libraries.Utils.String
import Libraries.Utils.Path
import Libraries.Data.String.Builder

%default covering

export
findChez : IO String
findChez
    = do Nothing <- idrisGetEnv "CHEZ"
            | Just chez => pure chez
         path <- pathLookup ["chez", "chezscheme", "chez-scheme", "chezscheme9.5", "scheme"]
         pure $ fromMaybe "/usr/bin/env scheme" path

||| Returns the chez scheme version for given executable
|||
||| This uses `chez --version` which unfortunately writes the version
||| on `stderr` thus requiring suffixing the command which shell redirection
||| which does not seem very portable.
export
chezVersion : String -> IO (Maybe Version)
chezVersion chez = do
    Right fh <- popen cmd Read
        | Left err => pure Nothing
    Right output <- fGetLine fh
        | Left err => pure Nothing
    ignore $ pclose fh
    pure $ parseVersion output
  where
  cmd : String
  cmd = chez ++ " --version 2>&1"

unsupportedCallingConvention : Maybe Version -> Bool
unsupportedCallingConvention Nothing = True
unsupportedCallingConvention (Just version) = version < MkVersion (9,5,0) Nothing

-- Given the chez compiler directives, return a list of pairs of:
--   - the library file name
--   - the full absolute path of the library file name, if it's in one
--     of the library paths managed by Idris
-- If it can't be found, we'll assume it's a system library and that chez
-- will thus be able to find it.
export
findLibs : {auto c : Ref Ctxt Defs} ->
           List String -> Core (List (String, String))
findLibs ds
    = do let libs = mapMaybe (isLib . trim) ds
         traverse locate (nub libs)
  where
    isLib : String -> Maybe String
    isLib d
        = if isPrefixOf "lib" d
             then Just (trim (substr 3 (length d) d))
             else Nothing

schHeader : String -> List String -> Bool -> Builder
schHeader chez libs whole
  = fromString $
    (if os /= "windows"
        then "#!" ++ chez ++ (if whole then " --program\n\n" else " --script\n\n")
        else "") ++ """
    ;; \{ generatedString "Chez" }
    (import (chezscheme))
    (case (machine-type)
      [(i3fb ti3fb a6fb ta6fb) #f]
      [(i3le ti3le a6le ta6le tarm64le)
         (with-exception-handler (lambda(x) (load-shared-object "libc.so"))
            (lambda () (load-shared-object "libc.so.6")))]
      [(i3osx ti3osx a6osx ta6osx tarm64osx tppc32osx tppc64osx) (load-shared-object "libc.dylib")]
      [(i3nt ti3nt a6nt ta6nt) (load-shared-object "msvcrt.dll")]
      [else (load-shared-object "libc.so")])

    \{ joinBy "\n" (map (\x => "(load-shared-object \"" ++ escapeStringChez x ++ "\")") libs) }

    \{ ifThenElse whole
                  "(let ()"
                  "(source-directories (cons (getenv \"IDRIS2_INC_SRC\") (source-directories)))"
     }

    """

schFooter : Bool -> Bool -> Builder
schFooter prof whole = fromString """

    (collect-request-handler (lambda () (collect (collect-maximum-generation)) (blodwen-run-finalisers)))
    (collect-rendezvous)
    \{ ifThenElse prof "(profile-dump-html)" "" }
    \{ ifThenElse whole ")" "" }
  """

showChezChar : Char -> Builder -> Builder
showChezChar '\\' acc = "\\\\" ++ acc
showChezChar c acc
   = if ord c < 32 || ord c > 126
        then fromString ("\\x" ++ asHex (cast c) ++ ";") ++ acc
        else char c ++ acc

showChezString : List Char -> Builder -> Builder
showChezString [] acc = acc
showChezString ('"' :: cs) acc = "\\\"" ++ showChezString cs acc
showChezString (c :: cs) acc = showChezChar c $ showChezString cs acc

export
chezString : String -> Builder
chezString cs = "\"" ++ showChezString (unpack cs) "\""

handleRet : CFType -> Builder -> Builder
handleRet CFUnit op = op ++ " " ++ mkWorld (schConstructor chezString (UN Underscore) (Just 0) [])
handleRet _ op = mkWorld op

getFArgs : NamedCExp -> Core (List (NamedCExp, NamedCExp))
getFArgs (NmCon fc _ _ (Just 0) _) = pure []
getFArgs (NmCon fc _ _ (Just 1) [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

export
chezExtPrim : SortedSet Name -> LazyExprProc -> Nat -> ExtPrim -> List NamedCExp -> Core Builder
chezExtPrim cs schLazy i GetField [NmPrimVal _ (Str s), _, _, struct,
                                   NmPrimVal _ (Str fld), _]
    = do structsc <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 struct
         pure $ "(ftype-ref " ++ fromString s ++ " (" ++ fromString fld ++ ") " ++ structsc ++ ")"
chezExtPrim cs schLazy i GetField [_,_,_,_,_,_]
    = pure "(blodwen-error-quit \"bad getField\")"
chezExtPrim cs schLazy i SetField [NmPrimVal _ (Str s), _, _, struct,
                        NmPrimVal _ (Str fld), _, val, world]
    = do structsc <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 struct
         valsc <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 val
         pure $ mkWorld $
            "(ftype-set! " ++ fromString s ++ " (" ++ fromString fld ++ ") " ++ structsc ++
            " " ++ valsc ++ ")"
chezExtPrim cs schLazy i SetField [_,_,_,_,_,_,_,_]
    = pure "(blodwen-error-quit \"bad setField\")"
chezExtPrim cs schLazy i SysCodegen []
    = pure $ "\"chez\""
chezExtPrim cs schLazy i OnCollect [_, p, c, world]
    = do p' <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 p
         c' <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 c
         pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
chezExtPrim cs schLazy i OnCollectAny [p, c, world]
    = do p' <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 p
         c' <- schExp cs (chezExtPrim cs schLazy) chezString schLazy 0 c
         pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
chezExtPrim cs schLazy i prim args
    = schExtCommon cs (chezExtPrim cs schLazy) chezString schLazy i prim args

-- Reference label for keeping track of loaded external libraries
export
data Loaded : Type where

-- Label for noting which struct types are declared
export
data Structs : Type where

cftySpec : FC -> CFType -> Core Builder
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFInt8 = pure "integer-8"
cftySpec fc CFInt16 = pure "integer-16"
cftySpec fc CFInt32 = pure "integer-32"
cftySpec fc CFInt64 = pure "integer-64"
cftySpec fc CFUnsigned8 = pure "unsigned-8"
cftySpec fc CFUnsigned16 = pure "unsigned-16"
cftySpec fc CFUnsigned32 = pure "unsigned-32"
cftySpec fc CFUnsigned64 = pure "unsigned-64"
cftySpec fc CFString = pure "string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "void*"
cftySpec fc CFGCPtr = pure "void*"
cftySpec fc CFBuffer = pure "u8*"
cftySpec fc (CFFun s t) = pure "void*"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ "(* " ++ fromString n ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

locateLib : {auto c : Ref Ctxt Defs} -> String -> String -> Core String
locateLib appdir clib
    = do (fname, fullname) <- locate clib
         copyLib (appdir </> fname, fullname)
         pure fname

export
loadLib : {auto c : Ref Ctxt Defs} ->
          String -> String -> Core String
loadLib appdir clib
    = do fname <- locateLib appdir clib
         pure $ "(load-shared-object \""
                                    ++ escapeStringChez fname
                                    ++ "\")\n"

loadSO : {auto c : Ref Ctxt Defs} ->
         String -> String -> Core String
loadSO appdir "" = pure ""
loadSO appdir mod
    = do d <- getDirs
         bdir <- ttcBuildDirectory
         allDirs <- extraSearchDirectories
         let fs = map (\p => p </> mod) (bdir :: allDirs)
         Just fname <- firstAvailable fs
            | Nothing => throw (InternalError ("Missing .so:" ++ mod))
         -- Easier to put them all in the same directory, so we don't need
         -- to traverse a directory tree when installing the executable. So,
         -- separate with '-' rather than directory separators.
         let modfname = fastConcat (intersperse "-" (splitPath mod))
         copyLib (appdir </> modfname, fname)
         pure $ "(load \"" ++ escapeStringChez modfname ++ "\")\n"

cCall : {auto c : Ref Ctxt Defs}
     -> {auto l : Ref Loaded (List String)}
     -> FC
     -> (cfn : String)
     -> (clib : String)
     -> List (Name, CFType)
     -> CFType
     -> (collectSafe : Bool)
     -> Core (Maybe String, Builder)
cCall fc cfn clib args (CFIORes CFGCPtr) _
    = throw (GenericMsg fc "Can't return GCPtr from a foreign function")
cCall fc cfn clib args CFGCPtr _
    = throw (GenericMsg fc "Can't return GCPtr from a foreign function")
cCall fc cfn clib args (CFIORes CFBuffer) _
    = throw (GenericMsg fc "Can't return Buffer from a foreign function")
cCall fc cfn clib args CFBuffer _
    = throw (GenericMsg fc "Can't return Buffer from a foreign function")
cCall fc cfn clib args ret collectSafe
    = do loaded <- get Loaded
         lib <- if clib `elem` loaded
                   then pure Nothing
                   else do put Loaded (clib :: loaded)
                           pure (Just clib)
         argTypes <- traverse (cftySpec fc . snd) args
         retType <- cftySpec fc ret
         let callConv : Builder = if collectSafe then " __collect_safe" else ""
         let call = "((foreign-procedure" ++ callConv ++ " " ++ showB cfn ++ " ("
                      ++ sepBy " " argTypes ++ ") " ++ retType ++ ") "
                      ++ sepBy " " !(traverse buildArg args) ++ ")"

         pure (lib, case ret of
                         CFIORes _ => handleRet ret call
                         _ => call)
  where
    mkNs : Int -> List CFType -> List (Maybe Builder)
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just (fromString $ "cb" ++ show i) :: mkNs (i + 1) xs

    applyLams : Builder -> List (Maybe Builder) -> Builder
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just a :: as) = applyLams ("(" ++ n ++ " " ++ a ++ ")") as

    getVal : Builder -> Builder
    getVal str = "(vector-ref " ++ str ++ "1)"

    mkFun : List CFType -> CFType -> Builder -> Builder
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ sepBy " " (catMaybes argns) ++ ") " ++
              (applyLams n argns ++ ")")

    notWorld : CFType -> Bool
    notWorld CFWorld = False
    notWorld _ = True

    callback : Builder -> List CFType -> CFType -> Core Builder
    callback n args (CFFun s t) = callback n (s :: args) t
    callback n args_rev retty
        = do let args = reverse args_rev
             argTypes <- traverse (cftySpec fc) (filter notWorld args)
             retType <- cftySpec fc retty
             pure $
                 "(let ([c-code (foreign-callable #f " ++
                       mkFun args retty n ++
                       " (" ++ sepBy " " argTypes ++ ") " ++ retType ++ ")])" ++
                       " (lock-object c-code) (foreign-callable-entry-point c-code))"

    buildArg : (Name, CFType) -> Core Builder
    buildArg (n, CFFun s t) = callback (schName n) [s] t
    buildArg (n, CFGCPtr) = pure $ "(car " ++ schName n ++ ")"
    buildArg (n, _) = pure $ schName n

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core Builder
schemeCall fc sfn argns ret
    = let call = "(" ++ fromString sfn ++ " " ++ sepBy " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => pure $ mkWorld call
               _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns any preamble needed for loading libraries, and the body of the
-- function call.
useCC : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> List String -> List (Name, CFType) -> CFType ->
        Maybe Version -> Core (Maybe String, Builder)
useCC fc ccs args ret version
    = case parseCC ["scheme,chez", "scheme", "C__collect_safe", "C"] ccs of
           Just ("scheme,chez", [sfn]) =>
               do body <- schemeCall fc sfn (map fst args) ret
                  pure (Nothing, body)
           Just ("scheme", [sfn]) =>
               do body <- schemeCall fc sfn (map fst args) ret
                  pure (Nothing, body)
           Just ("C__collect_safe", (cfn :: clib :: _)) => do
             if unsupportedCallingConvention version
               then cCall fc cfn clib args ret False
               else cCall fc cfn clib args ret True
           Just ("C", (cfn :: clib :: _)) =>
             cCall fc cfn clib args ret False
           _ => throw (NoForeignCC fc ccs)

-- For every foreign arg type, return a name, and whether to pass it to the
-- foreign call (we don't pass '%World')
mkArgs : Int -> List CFType -> List (Name, Bool)
mkArgs i [] = []
mkArgs i (CFWorld :: cs) = (MN "farg" i, False) :: mkArgs i cs
mkArgs i (c :: cs) = (MN "farg" i, True) :: mkArgs (i + 1) cs

mkStruct : {auto s : Ref Structs (List String)} ->
           CFType -> Core Builder
mkStruct (CFStruct n flds)
    = do defs <- traverse mkStruct (map snd flds)
         strs <- get Structs
         if n `elem` strs
            then pure (concat defs)
            else do put Structs (n :: strs)
                    pure $ concat defs ++ "(define-ftype " ++ fromString n ++ " (struct\n\t"
                           ++ sepBy "\n\t" !(traverse showFld flds) ++ "))\n"
  where
    showFld : (String, CFType) -> Core Builder
    showFld (n, ty) = pure $ "[" ++ fromString n ++ " " ++ !(cftySpec emptyFC ty) ++ "]"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = do [| mkStruct a ++ mkStruct b |]
mkStruct _ = pure ""

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            FC -> Name -> NamedDef -> Maybe Version ->
            Core (Maybe String, Builder)
schFgnDef fc n (MkNmForeign cs args ret) version
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (load, body) <- useCC fc cs (zip useargns args) ret version
         defs <- get Ctxt
         pure (load,
                concat argStrs ++ retStr ++
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ sepBy " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ _ = pure (Nothing, "")

export
getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             Maybe Version -> (Name, FC, NamedDef) ->
             Core (Maybe String, Builder)
getFgnCall version (n, fc, d) = schFgnDef fc n d version

export
startChezPreamble : String
startChezPreamble = """
  #!/bin/sh
  # \{ generatedString "Chez" }

  set -e # exit on any error

  if [ "$(uname)" = Darwin ]; then
    DIR=$(zsh -c 'printf %s "$0:A:h"' "$0")
  else
    DIR=$(dirname "$(readlink -f -- "$0")")
  fi

  """

startChez : String -> String -> String
startChez appdir target = startChezPreamble ++ """
  export LD_LIBRARY_PATH="$DIR/\{ appdir }:$LD_LIBRARY_PATH"
  export DYLD_LIBRARY_PATH="$DIR/\{ appdir }:$DYLD_LIBRARY_PATH"
  export IDRIS2_INC_SRC="$DIR/\{ appdir }"

  "$DIR/\{ target }" "$@"
  """

startChezCmd : String -> String -> String -> String -> String
startChezCmd chez appdir target progType = """
  @echo off

  rem \{ generatedString "Chez" }

  set APPDIR=%~dp0
  set PATH=%APPDIR%\{ appdir };%PATH%
  set IDRIS2_INC_SRC=%APPDIR%\{ appdir }

  "\{ chez }" \{ progType } "%APPDIR%\{ target }" %*
  """

startChezWinSh : String -> String -> String -> String -> String
startChezWinSh chez appdir target progType = """
  #!/bin/sh
  # \{ generatedString "Chez" }

  set -e # exit on any error

  DIR=$(dirname "$(readlink -f -- "$0" || cygpath -a -- "$0")")
  PATH="$DIR/\{ appdir }:$PATH"

  export IDRIS2_INC_SRC="$DIR/\{ appdir }"

  "\{ chez }" \{ progType } "$DIR/\{ target }" "$@"
  """

-- This handler turned out to be much more effective than the original simple
-- `(collect-request-handler (lambda () (collect) (blodwen-run-finalisers)))`
export
collectRequestHandler : Builder
collectRequestHandler = """
  (collect-request-handler
    (let* ([gc-counter 1]
           [log-radix 2]
           [radix-mask (sub1 (bitwise-arithmetic-shift 1 log-radix))]
           [major-gc-factor 2]
           [trigger-major-gc-allocated (* major-gc-factor (bytes-allocated))])
      (lambda ()
        (cond
          [(>= (bytes-allocated) trigger-major-gc-allocated)
           ;; Force a major collection if memory use has doubled
           (collect (collect-maximum-generation))
           (blodwen-run-finalisers)
           (set! trigger-major-gc-allocated (* major-gc-factor (bytes-allocated)))]
          [else
           ;; Imitate the built-in rule, but without ever going to a major collection
           (let ([this-counter gc-counter])
             (if (> (add1 this-counter)
                    (bitwise-arithmetic-shift-left 1 (* log-radix (sub1 (collect-maximum-generation)))))
                 (set! gc-counter 1)
                 (set! gc-counter (add1 this-counter)))
             (collect
              ;; Find the minor generation implied by the counter
              (let loop ([c this-counter] [gen 0])
                (cond
                  [(zero? (bitwise-and c radix-mask))
                   (loop (bitwise-arithmetic-shift-right c log-radix)
                         (add1 gen))]
                  [else
                   gen]))))]))))
  """

||| Compile a TT expression to Chez Scheme
compileToSS : Ref Ctxt Defs ->
              Bool -> -- profiling
              String -> ClosedTerm -> (outfile : String) -> Core ()
compileToSS c prof appdir tm outfile
    = do ds <- getDirectives Chez
         libs <- findLibs ds
         traverse_ copyLib libs
         cdata <- getCompileData False Cases tm
         let ndefs = namedDefs cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         l <- newRef {t = List String} Loaded ["libc", "libc 6"]
         s <- newRef {t = List String} Structs []
         chez <- coreLift findChez
         version <- coreLift $ chezVersion chez
         fgndefs <- traverse (getFgnCall version) ndefs
         loadlibs <- traverse (locateLib appdir) (mapMaybe fst fgndefs)

         let schLazy = if getWeakMemoLazy ds then weakMemoLaziness else defaultLaziness

         (sortedDefs, constants) <- sortDefs ndefs
         compdefs <- logTime 3 "Print as scheme" $ traverse (getScheme constants (chezExtPrim constants schLazy) chezString schLazy) sortedDefs
         let code = concat (map snd fgndefs) ++ concat compdefs
         main <- schExp constants (chezExtPrim constants schLazy) chezString schLazy 0 ctm
         support <- readDataFile "chez/support.ss"
         extraRuntime <- getExtraRuntime ds
         let scm = concat $ the (List _)
                   [ schHeader chez (map snd libs ++ loadlibs) True
                   , fromString support
                   , fromString extraRuntime
                   , code
                   , collectRequestHandler ++ "\n"
                   , main
                   , schFooter prof True
                   ]
         Right () <- coreLift $ writeFile outfile $ build scm
            | Left err => throw (FileErr outfile err)
         coreLift_ $ chmodRaw outfile 0o755

||| Compile a Chez Scheme source file to an executable, daringly with runtime checks off.
compileToSO : {auto c : Ref Ctxt Defs} ->
              Bool -> -- profiling
              String -> (appDirRel : String) -> (outSsAbs : String) -> Core ()
compileToSO prof chez appDirRel outSsAbs
    = do let tmpFileAbs = appDirRel </> "compileChez"
         let build = "(parameterize ([optimize-level 3] "
                     ++ (if prof then "[compile-profile #t] "
                                else "") ++
                     "[compile-file-message #f]) (compile-program " ++
                    show outSsAbs ++ "))"
         Right () <- coreLift $ writeFile tmpFileAbs build
            | Left err => throw (FileErr tmpFileAbs err)
         coreLift_ $ chmodRaw tmpFileAbs 0o755
         0 <- coreLift $ system [chez, "--script", tmpFileAbs]
            | status => throw (InternalError "Chez exited with return code \{show status}")
         pure ()

||| Compile a TT expression to Chez Scheme using incremental module builds
compileToSSInc : Ref Ctxt Defs ->
                 List String -> -- module so files
                 List String -> -- libraries to find and load
                 String -> ClosedTerm -> (outfile : String) -> Core ()
compileToSSInc c mods libs appdir tm outfile
    = do chez <- coreLift findChez
         tmcexp <- compileTerm tm
         let ctm = forget tmcexp

         loadlibs <- traverse (map fromString . loadLib appdir) (nub libs)
         loadsos <- traverse (map fromString . loadSO appdir) (nub mods)

         main <- schExp empty (chezExtPrim empty defaultLaziness) chezString defaultLaziness 0 ctm
         support <- readDataFile "chez/support.ss"

         let scm = schHeader chez [] False ++
                   fromString support ++
                   concat loadlibs ++
                   concat loadsos ++
                   collectRequestHandler ++ "\n" ++
                   main ++ schFooter False False

         Right () <- coreLift $ writeFile outfile $ build scm
            | Left err => throw (FileErr outfile err)
         coreLift_ $ chmodRaw outfile 0o755
         pure ()


makeSh : String -> String -> String -> Core ()
makeSh outShRel appdir outAbs
    = do Right () <- coreLift $ writeFile outShRel (startChez appdir outAbs)
            | Left err => throw (FileErr outShRel err)
         pure ()

||| Make Windows start scripts, one for bash environments and one batch file
makeShWindows : String -> String -> String -> String -> String -> Core ()
makeShWindows chez outShRel appdir outAbs progType
    = do let cmdFile = outShRel ++ ".cmd"
         Right () <- coreLift $ writeFile cmdFile (startChezCmd chez appdir outAbs progType)
            | Left err => throw (FileErr cmdFile err)
         Right () <- coreLift $ writeFile outShRel (startChezWinSh chez appdir outAbs progType)
            | Left err => throw (FileErr outShRel err)
         pure ()

compileExprWhole :
  Bool ->
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExprWhole makeitso c s tmpDir outputDir tm outfile
    = do let appDirRel = outfile ++ "_app" -- relative to build dir
         let appDirGen = outputDir </> appDirRel -- relative to here
         coreLift_ $ mkdirAll appDirGen
         Just cwd <- coreLift currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         let outSsFile = appDirRel </> outfile <.> "ss"
         let outSoFile = appDirRel </> outfile <.> "so"
         let outSsAbs = cwd </> outputDir </> outSsFile
         let outSoAbs = cwd </> outputDir </> outSoFile
         chez <- coreLift $ findChez
         let prof = profile !getSession
         logTime 2 "Compile to scheme" $ compileToSS c (makeitso && prof) appDirGen tm outSsAbs
         logTime 2 "Make SO" $ when makeitso $
           compileToSO prof chez appDirGen outSsAbs
         let outShRel = outputDir </> outfile
         if isWindows
            then makeShWindows chez outShRel appDirRel (if makeitso then outSoFile else outSsFile) "--program"
            else makeSh outShRel appDirRel (if makeitso then outSoFile else outSsFile)
         coreLift_ $ chmodRaw outShRel 0o755
         pure (Just outShRel)

compileExprInc :
  Bool ->
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExprInc makeitso c s tmpDir outputDir tm outfile
    = do defs <- get Ctxt
         let Just (mods, libs) = lookup Chez (allIncData defs)
             | Nothing =>
                 do coreLift $ putStrLn $ "Missing incremental compile data, reverting to whole program compilation"
                    compileExprWhole makeitso c s tmpDir outputDir tm outfile
         let appDirRel = outfile ++ "_app" -- relative to build dir
         let appDirGen = outputDir </> appDirRel -- relative to here
         coreLift_ $ mkdirAll appDirGen
         Just cwd <- coreLift currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         let outSsFile = appDirRel </> outfile <.> "ss"
         let outSoFile = appDirRel </> outfile <.> "so"
         let outSsAbs = cwd </> outputDir </> outSsFile
         let outSoAbs = cwd </> outputDir </> outSoFile
         chez <- coreLift $ findChez
         compileToSSInc c mods libs appDirGen tm outSsAbs
         let outShRel = outputDir </> outfile
         if isWindows
            then makeShWindows chez outShRel appDirRel outSsFile "--script"
            else makeSh outShRel appDirRel outSsFile
         coreLift_ $ chmodRaw outShRel 0o755
         pure (Just outShRel)

||| Chez Scheme implementation of the `compileExpr` interface.
compileExpr :
  Bool ->
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr makeitso c s tmpDir outputDir tm outfile
    = do sesh <- getSession
         if not (wholeProgram sesh) && (Chez `elem` incrementalCGs sesh)
            then compileExprInc makeitso c s tmpDir outputDir tm outfile
            else compileExprWhole makeitso c s tmpDir outputDir tm outfile

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

incCompile :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (sourceFile : String) -> Core (Maybe (String, List String))
incCompile c s sourceFile
    = do
         ssFile <- getTTCFileName sourceFile "ss"
         soFile <- getTTCFileName sourceFile "so"
         soFilename <- getObjFileName sourceFile "so"
         cdata <- getIncCompileData False Cases

         d <- getDirs
         outputDir <- ttcBuildDirectory

         let ndefs = namedDefs cdata
         if isNil ndefs
            then pure (Just ("", []))
                      -- ^ no code to generate, but still recored that the
                      -- module has been compiled, with no output needed.
            else do
               l <- newRef {t = List String} Loaded ["libc", "libc 6"]
               s <- newRef {t = List String} Structs []
               chez <- coreLift findChez
               version <- coreLift $ chezVersion chez
               fgndefs <- traverse (getFgnCall version) ndefs
               (sortedDefs, constants) <- sortDefs ndefs
               compdefs <- traverse (getScheme empty (chezExtPrim empty defaultLaziness) chezString defaultLaziness) sortedDefs
               let code = concat $ map snd fgndefs ++ compdefs
               Right () <- coreLift $ writeFile ssFile $ build code
                  | Left err => throw (FileErr ssFile err)

               -- Compile to .so
               let tmpFileAbs = outputDir </> "compileChez"
               let build = "(parameterize ([optimize-level 3] " ++
                           "[compile-file-message #f]) (compile-file " ++
                          show ssFile ++ "))"
               Right () <- coreLift $ writeFile tmpFileAbs build
                  | Left err => throw (FileErr tmpFileAbs err)
               0 <- coreLift $ system [chez, "--script", tmpFileAbs]
                  | status => throw (InternalError "Chez exited with return code \{show status}")
               pure (Just (soFilename, mapMaybe fst fgndefs))

||| Codegen wrapper for Chez scheme implementation.
export
codegenChez : Codegen
codegenChez = MkCG (compileExpr True) executeExpr (Just incCompile) (Just "so")
