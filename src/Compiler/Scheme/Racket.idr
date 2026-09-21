module Compiler.Scheme.Racket

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
import Data.String
import Data.SortedSet

import System
import System.Directory
import System.Info

import Libraries.Data.String.Builder
import Libraries.Utils.Path

%default covering

findRacket : IO String
findRacket =
  do env <- idrisGetEnv "RACKET"
     pure $ fromMaybe "/usr/bin/env racket" env

findRacoExe : IO (List String)
findRacoExe =
  do env <- idrisGetEnv "RACKET_RACO"
     pure $ (maybe ["/usr/bin/env", "raco"] singleton env) ++ ["exe"]

schHeader : Bool -> Builder -> Builder
schHeader prof libs = fromString """
  #lang racket/base
  ;; \{ generatedString "Racket" }
  (require racket/async-channel)         ; for asynchronous channels
  (require racket/future)                ; for parallelism/concurrency
  (require racket/math)                  ; for math ops
  (require racket/promise)               ; for delay/force in toplevel defs
  (require racket/system)                ; for system
  (require racket/unsafe/ops)            ; for fast fixnum ops
  (require rnrs/bytevectors-6)           ; for buffers
  (require rnrs/io/ports-6)              ; for files
  (require srfi/19)                      ; for file handling and data
  (require ffi/unsafe ffi/unsafe/define) ; for calling C
  \{ ifThenElse prof "(require profile)" "" }
  (require racket/flonum)                ; for float-typed transcendental functions
  (require math/flonum)                  ; for flonum constants

  """ ++ libs ++ """

  (let ()

  """

schFooter : Builder
schFooter = """
  )
  (collect-garbage)
  """

showRacketChar : Char -> Builder -> Builder
showRacketChar '\\' acc = "\\\\" ++ acc
showRacketChar c acc
   = if ord c < 32 || ord c > 126
        then fromString ("\\u" ++ leftPad '0' 4 (asHex (cast c))) ++ acc
        else char c ++ acc

showRacketString : List Char -> Builder -> Builder
showRacketString [] acc = acc
showRacketString ('"' :: cs) acc = "\\\"" ++ showRacketString cs acc
showRacketString (c :: cs) acc = showRacketChar c $ showRacketString cs acc

racketString : String -> Builder
racketString cs = "\"" ++ showRacketString (unpack cs) "\""

racketPrim : SortedSet Name -> LazyExprProc -> Nat -> ExtPrim -> List NamedCExp -> Core Builder
racketPrim cs schLazy i GetField [NmPrimVal _ (Str s), _, _, struct,
                       NmPrimVal _ (Str fld), _]
    = do structsc <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 struct
         pure $ "(" ++ fromString s ++ "-" ++ fromString fld ++ " " ++ structsc ++ ")"
racketPrim cs schLazy i GetField [_,_,_,_,_,_]
    = pure "(error \"bad getField\")"
racketPrim cs schLazy i SetField [NmPrimVal _ (Str s), _, _, struct,
                       NmPrimVal _ (Str fld), _, val, world]
    = do structsc <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 struct
         valsc <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 val
         pure $ mkWorld $
              "(set-" ++ fromString s ++ "-" ++ fromString fld ++ "! " ++ structsc ++ " " ++ valsc ++ ")"
racketPrim cs schLazy i SetField [_,_,_,_,_,_,_,_]
    = pure "(error \"bad setField\")"
racketPrim cs schLazy i SysCodegen []
    = pure $ "\"racket\""
racketPrim cs schLazy i OnCollect [_, p, c, world]
    = do p' <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 p
         c' <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 c
         pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
racketPrim cs schLazy i OnCollectAny [p, c, world]
    = do p' <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 p
         c' <- schExp cs (racketPrim cs schLazy) racketString schLazy 0 c
         pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
racketPrim cs schLazy i prim args
    = schExtCommon cs (racketPrim cs schLazy) racketString schLazy i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

-- Label for noting which foreign names are declared
data Done : Type where

cftySpec : FC -> CFType -> Core Builder
cftySpec fc CFUnit = pure "_void"
cftySpec fc CFInt = pure "_int"
cftySpec fc CFInt8 = pure "_int8"
cftySpec fc CFInt16 = pure "_int16"
cftySpec fc CFInt32 = pure "_int32"
cftySpec fc CFInt64 = pure "_int64"
cftySpec fc CFUnsigned8 = pure "_uint8"
cftySpec fc CFUnsigned16 = pure "_uint16"
cftySpec fc CFUnsigned32 = pure "_uint32"
cftySpec fc CFUnsigned64 = pure "_uint64"
cftySpec fc CFString = pure "_string/utf-8"
cftySpec fc CFDouble = pure "_double"
cftySpec fc CFChar = pure "_int8"
cftySpec fc CFPtr = pure "_pointer"
cftySpec fc CFGCPtr = pure "_pointer"
cftySpec fc CFBuffer = pure "_bytes"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ "_" ++ fromString n ++ "-pointer"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core Builder
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse args)
             pure $ "(_fun " ++ sepBy " " argspecs ++ " -> " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

loadlib : String -> String -> String
loadlib "libc" _ = "(define-ffi-definer define-libc (ffi-lib #f))\n"
loadlib libn ver
    = "(define-ffi-definer define-" ++ libn ++
      " (ffi-lib \"" ++ libn ++ "\" " ++ ver ++ "))\n"

getLibVers : String -> (String, String)
getLibVers libspec
    = case words libspec of
           [] => ("", "")
           [fn] => case span (/='.') libspec of
                        (root, rest) => (root, "")
           (fn :: vers) =>
               (fst (span (/='.') fn),
                  "'(" ++ joinBy " " (map show vers) ++ " #f)" )

cToRkt : CFType -> Builder -> Builder
cToRkt CFChar op = "(integer->char " ++ op ++ ")"
cToRkt _ op = op

rktToC : CFType -> Builder -> Builder
rktToC CFChar op = "(char->integer " ++ op ++ ")"
rktToC _ op = op

handleRet : CFType -> Builder -> Builder
handleRet CFUnit op = op ++ " " ++ mkWorld (schConstructor racketString (UN $ Basic "") (Just 0) [])
handleRet ret op = mkWorld (cToRkt ret op)

cCall : {auto f : Ref Done (List String) } ->
        {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        String -> FC -> (cfn : String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core (Builder, Builder)
cCall appdir fc cfn clib args (CFIORes CFGCPtr)
    = throw (GenericMsg fc "Can't return GCPtr from a foreign function")
cCall appdir fc cfn clib args CFGCPtr
    = throw (GenericMsg fc "Can't return GCPtr from a foreign function")
cCall appdir fc cfn clib args (CFIORes CFBuffer)
    = throw (GenericMsg fc "Can't return Buffer from a foreign function")
cCall appdir fc cfn clib args CFBuffer
    = throw (GenericMsg fc "Can't return Buffer from a foreign function")
cCall appdir fc cfn libspec args ret
    = do loaded <- get Loaded
         bound <- get Done

         let (libn, vers) = getLibVers libspec
         lib <- if libn `elem` loaded
                   then pure ""
                   else do put Loaded (libn :: loaded)
                           (fname, fullname) <- locate libspec
                           copyLib (appdir </> fname, fullname)
                           pure (loadlib libn vers)

         argTypes <- traverse (\a => do s <- cftySpec fc (snd a)
                                        pure (a, s)) args
         retType <- cftySpec fc ret
         cbind <- if cfn `elem` bound
                     then pure ""
                     else do put Done (cfn :: bound)
                             pure $ "(define-" ++ fromString libn ++ " " ++ fromString cfn ++
                                    " (_fun " ++ sepBy " " (map snd argTypes) ++ " -> " ++
                                        retType ++ "))\n"
         let call = "(" ++ fromString cfn ++ " " ++
                    sepBy " " !(traverse useArg (map fst argTypes)) ++ ")"

         pure (fromString lib ++ cbind, case ret of
                                  CFIORes rt => handleRet rt call
                                  _ => call)
  where
    mkNs : Int -> List CFType -> List (Maybe (Builder, CFType))
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just (fromString ("cb" ++ show i), x) :: mkNs (i + 1) xs

    applyLams : Builder -> List (Maybe (Builder, CFType)) -> Builder
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just (a, ty) :: as)
        = applyLams ("(" ++ n ++ " " ++ cToRkt ty a ++ ")") as

    mkFun : List CFType -> CFType -> Builder -> Builder
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ sepBy " " (map fst (catMaybes argns)) ++ ") " ++
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
             pure $ mkFun args retty n

    useArg : (Name, CFType) -> Core Builder
    useArg (n, CFFun s t) = callback (schName n) [s] t
    useArg (n, ty)
        = pure $ rktToC ty (schName n)

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Builder
schemeCall fc sfn argns ret
    = let call = "(" ++ fromString sfn ++ " " ++ sepBy " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => mkWorld call
               _ => call

-- Use a calling convention to compile a foreign def.
-- Returns any preamble needed for loading libraries, and the body of the
-- function call.
useCC : {auto f : Ref Done (List String) } ->
        {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        String -> FC -> List String -> List (Name, CFType) -> CFType -> Core (Builder, Builder)
useCC appdir fc ccs args ret
    = case parseCC ["scheme,racket", "scheme", "C"] ccs of
           Nothing => throw (NoForeignCC fc ccs)
           Just ("scheme,racket", [sfn]) =>
               do let body = schemeCall fc sfn (map fst args) ret
                  pure ("", body)
           Just ("scheme,racket", [sfn, racketlib]) =>
               do let body = schemeCall fc sfn (map fst args) ret
                  pure (fromString $ "(require " ++ racketlib ++ ")", body)
           Just ("scheme", [sfn]) =>
               do let body = schemeCall fc sfn (map fst args) ret
                  pure ("", body)
           Just ("C", [cfn, clib]) => cCall appdir fc cfn clib args ret
           Just ("C", [cfn, clib, chdr]) => cCall appdir fc cfn clib args ret
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
                    pure $ concat defs ++ "(define-cstruct _" ++ fromString n ++ " ("
                           ++ sepBy "\n\t" !(traverse showFld flds) ++ "))\n"
  where
    showFld : (String, CFType) -> Core Builder
    showFld (n, ty) = pure $ "[" ++ fromString n ++ " " ++ !(cftySpec emptyFC ty) ++ "]"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = [| mkStruct a ++ mkStruct b |]
mkStruct _ = pure ""

schFgnDef : {auto f : Ref Done (List String) } ->
            {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            String -> FC -> Name -> NamedDef -> Core (Builder, Builder)
schFgnDef appdir fc n (MkNmForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (load, body) <- useCC appdir fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (concat argStrs ++ retStr ++ load,
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ sepBy " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ _ = pure ("", "")

getFgnCall : {auto f : Ref Done (List String) } ->
             {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             String -> (Name, FC, NamedDef) -> Core (Builder, Builder)
getFgnCall appdir (n, fc, d) = schFgnDef appdir fc n d

startRacket : String -> String -> String -> String
startRacket racket appdir target = """
  #!/bin/sh
  # \{ generatedString "Racket" }

  set -e # exit on any error

  if [ "$(uname)" = Darwin ]; then
    DIR=$(zsh -c 'printf %s "$0:A:h"' "$0")
  else
    DIR=$(dirname "$(readlink -f -- "$0")")
  fi

  export LD_LIBRARY_PATH="$DIR/\{ appdir }:$LD_LIBRARY_PATH"
  export DYLD_LIBRARY_PATH="$DIR/\{ appdir }:$DYLD_LIBRARY_PATH"

  \{ racket } "$DIR/\{ target }" "$@"
  """

startRacketCmd : String -> String -> String -> String
startRacketCmd racket appdir target = """
  @echo off

  rem \{ generatedString "Racket" }

  set APPDIR=%~dp0
  set PATH=%APPDIR%\{ appdir };%PATH%

  \{ racket } "%APPDIR%\{ target }" %*
  """

startRacketWinSh : String -> String -> String -> String
startRacketWinSh racket appdir target = """
  #!/bin/sh
  # \{ generatedString "Racket" }

  set -e # exit on any error

  DIR=$(dirname "$(readlink -f -- "$0" || cygpath -a -- "$0")")
  PATH="$DIR/\{ appdir }:$PATH"

  \{ racket } "$DIR/\{ target }" "$@"
  """

compileToRKT : Ref Ctxt Defs ->
               String -> ClosedTerm -> (outfile : String) -> Core ()
compileToRKT c appdir tm outfile
    = do cdata <- getCompileData False Cases tm
         let ndefs = namedDefs cdata
         let ctm = forget (mainExpr cdata)

         ds <- getDirectives Racket
         let schLazy = if getWeakMemoLazy ds then weakMemoLaziness else defaultLaziness

         defs <- get Ctxt
         f <- newRef {t = List String} Done empty
         l <- newRef {t = List String} Loaded []
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse (getFgnCall appdir) ndefs
         (sortedDefs, constants) <- sortDefs ndefs
         compdefs <- traverse (getScheme constants (racketPrim constants schLazy) racketString schLazy) sortedDefs
         let code = concat (map snd fgndefs) ++ concat compdefs
         main <- schExp constants (racketPrim constants schLazy) racketString schLazy 0 ctm
         support <- readDataFile "racket/support.rkt"
         extraRuntime <- getExtraRuntime ds
         let prof = profile !getSession
         let runmain
                = if prof
                     then "(profile (void " ++ main ++ ") #:order 'self)\n"
                     else "(void " ++ main ++ ")\n"
         let scm = schHeader prof (concat (map fst fgndefs)) ++
                   fromString support ++ fromString extraRuntime ++ code ++
                   runmain ++ schFooter
         Right () <- coreLift $ writeFile outfile $ build scm
            | Left err => throw (FileErr outfile err)
         coreLift_ $ chmodRaw outfile 0o755
         pure ()

makeSh : String -> String -> String -> String -> Core ()
makeSh racket outShRel appdir outAbs
    = do Right () <- coreLift $ writeFile outShRel (startRacket racket appdir outAbs)
            | Left err => throw (FileErr outShRel err)
         pure ()

||| Make Windows start scripts, one for bash environments and one batch file
makeShWindows : String -> String -> String -> String -> Core ()
makeShWindows racket outShRel appdir outAbs
    = do let cmdFile = outShRel ++ ".cmd"
         Right () <- coreLift $ writeFile cmdFile (startRacketCmd racket appdir outAbs)
            | Left err => throw (FileErr cmdFile err)
         Right () <- coreLift $ writeFile outShRel (startRacketWinSh racket appdir outAbs)
            | Left err => throw (FileErr outShRel err)
         pure ()

compileExpr :
  Bool ->
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (outputDir : String) ->
  ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr mkexec c s tmpDir outputDir tm outfile
    = do let appDirRel = outfile ++ "_app" -- relative to build dir
         let appDirGen = outputDir </> appDirRel -- relative to here
         coreLift_ $ mkdirAll appDirGen
         Just cwd <- coreLift currentDir
              | Nothing => throw (InternalError "Can't get current directory")

         let ext = if isWindows then ".exe" else ""
         let outRktFile = appDirRel </> outfile <.> "rkt"
         let outBinFile = appDirRel </> outfile <.> ext
         let outRktAbs = cwd </> outputDir </> outRktFile
         let outBinAbs = cwd </> outputDir </> outBinFile

         compileToRKT c appDirGen tm outRktAbs
         raco <- coreLift findRacoExe
         racket <- coreLift findRacket

         ok <- the (Core Int) $ if mkexec
                  then logTime 1 "Build racket" $
                         coreLift $ system $ raco ++ ["-o", outBinAbs, outRktAbs]
                  else pure 0
         if ok == 0
            then do -- TODO: add launcher script
                    let outShRel = outputDir </> outfile
                    if isWindows
                       then if mkexec
                               then makeShWindows "" outShRel appDirRel outBinFile
                               else makeShWindows (racket ++ " ") outShRel appDirRel outRktFile
                       else if mkexec
                               then makeSh "" outShRel appDirRel outBinFile
                               else makeSh (racket ++ " ") outShRel appDirRel outRktFile
                    coreLift_ $ chmodRaw outShRel 0o755
                    pure (Just outShRel)
            else pure Nothing

executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm
    = do Just sh <- compileExpr False c s tmpDir tmpDir tm "_tmpracket"
            | Nothing => throw (InternalError "compileExpr returned Nothing")
         coreLift_ $ system [sh]

export
codegenRacket : Codegen
codegenRacket = MkCG (compileExpr True) executeExpr Nothing Nothing
