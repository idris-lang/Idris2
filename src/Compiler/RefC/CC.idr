module Compiler.RefC.CC

import Core.Context
import Core.Context.Log
import Core.Options
import Core.Directory

import System
import Idris.Env

import Data.String

%default total

findCC : IO String
findCC
    = do Nothing <- idrisGetEnv "IDRIS2_CC"
           | Just cc => pure cc
         Nothing <- idrisGetEnv "CC"
           | Just cc => pure cc
         pure "cc"

findCFLAGS : IO String
findCFLAGS
  = do Nothing <- idrisGetEnv "IDRIS2_CFLAGS"
         | Just cflags => pure cflags
       Nothing <- idrisGetEnv "CFLAGS"
         | Just cflags => pure cflags
       pure ""

findCPPFLAGS : IO String
findCPPFLAGS
  = do Nothing <- idrisGetEnv "IDRIS2_CPPFLAGS"
         | Just cppflags => pure cppflags
       Nothing <- idrisGetEnv "CPPFLAGS"
         | Just cppflags => pure cppflags
       pure ""

findLDFLAGS : IO String
findLDFLAGS
  = do Nothing <- idrisGetEnv "IDRIS2_LDFLAGS"
         | Just ldflags => pure ldflags
       Nothing <- idrisGetEnv "LDFLAGS"
         | Just ldflags => pure ldflags
       pure ""

findLDLIBS : IO String
findLDLIBS
  = do Nothing <- idrisGetEnv "IDRIS2_LDLIBS"
         | Just ldlibs => pure ldlibs
       Nothing <- idrisGetEnv "LDLIBS"
         | Just ldlibs => pure ldlibs
       pure ""


clibdirs : List String -> List String
clibdirs ds = map (\d => "-L" ++ d) ds

-- cincdirs : List String -> String
-- cincdirs ds = concat (map (\d => "-I" ++ d ++ " ") ds)

-- Extract the value after "key=" from a directive string, or Nothing.
directiveValue : String -> String -> Maybe String
directiveValue key d =
    if isPrefixOf (key ++ "=") d
    then Just (substr (length (key ++ "=")) (length d) d)
    else Nothing

-- Build cross-compilation flags from directives and environment variables:
--   directive "target=<triple>"  / env IDRIS2_CROSS_TRIPLE -> "--target=<triple>"
--   directive "sysroot=<path>"   / env IDRIS2_SYSROOT      -> "--sysroot=<path>"
-- These flags are passed to both the compile and link invocations so that
-- clang/gcc can generate code and find libraries for the target system.
crossCompileFlags : {auto c : Ref Ctxt Defs} -> List String -> Core (List String)
crossCompileFlags directives = do
    target  <- case mapMaybe (directiveValue "target")  directives of
                 (t :: _) => pure (Just t)
                 []       => coreLift $ idrisGetEnv "IDRIS2_CROSS_TRIPLE"
    sysroot <- case mapMaybe (directiveValue "sysroot") directives of
                 (s :: _) => pure (Just s)
                 []       => coreLift $ idrisGetEnv "IDRIS2_SYSROOT"
    pure $ maybe [] (\t => ["--target=" ++ t]) target
        ++ maybe [] (\s => ["--sysroot=" ++ s]) sysroot

-- True when the effective target triple looks like a WebAssembly target.
isWasmTarget : List String -> IO Bool
isWasmTarget directives = do
    triple <- case mapMaybe (directiveValue "target") directives of
                (t :: _) => pure (Just t)
                []       => idrisGetEnv "IDRIS2_CROSS_TRIPLE"
    pure $ case triple of
        Just t  => isPrefixOf "wasm32" t || isPrefixOf "wasm64" t
        Nothing => False

-- True when GMP should be disabled: explicit directive, WASM target, or env var.
needsNoGmp : List String -> IO Bool
needsNoGmp directives = do
    wasm <- isWasmTarget directives
    env  <- idrisGetEnv "IDRIS2_NO_GMP"
    pure $ wasm || elem "no-gmp" directives || isJust env

-- True when libffi should be omitted from the link.
needsNoFfi : List String -> IO Bool
needsNoFfi directives = do
    wasm <- isWasmTarget directives
    env  <- idrisGetEnv "IDRIS2_NO_FFI"
    pure $ wasm || elem "no-ffi" directives || isJust env

-- True when pthreads should be disabled.
needsNoThreads : List String -> IO Bool
needsNoThreads directives = do
    wasm <- isWasmTarget directives
    env  <- idrisGetEnv "IDRIS2_NO_THREADS"
    pure $ wasm || elem "no-threads" directives || isJust env

-- Find the directory containing libidris2_refc, with optional override.
-- directive "refc-lib-dir=<path>"  / env IDRIS2_REFC_LIB_DIR override the
-- installed refc data directory so WASM (or other cross) builds can supply
-- their own pre-built runtime.
findRefcLibDir : {auto c : Ref Ctxt Defs} -> List String -> Core String
findRefcLibDir directives =
    case mapMaybe (directiveValue "refc-lib-dir") directives of
        (d :: _) => pure d
        [] => do
            env <- coreLift $ idrisGetEnv "IDRIS2_REFC_LIB_DIR"
            case env of
                Just d  => pure d
                Nothing => findDataFile "refc"

-- Find libidris2_support.a, with optional override.
-- directive "support-lib=<path>"  / env IDRIS2_REFC_SUPPORT_LIB let a WASM
-- (or cross) build supply a pre-compiled version of the support library.
findSupportLib : {auto c : Ref Ctxt Defs} -> List String -> Core String
findSupportLib directives =
    case mapMaybe (directiveValue "support-lib") directives of
        (d :: _) => pure d
        [] => do
            env <- coreLift $ idrisGetEnv "IDRIS2_REFC_SUPPORT_LIB"
            case env of
                Just d  => pure d
                Nothing => findLibraryFile "libidris2_support.a"

export
compileCObjectFile : {auto c : Ref Ctxt Defs}
                  -> {default False asLibrary : Bool}
                  -> (sourceFile : String)
                  -> (objectFile : String)
                  -> Core (Maybe String)
compileCObjectFile {asLibrary} sourceFile objectFile =
  do cc <- coreLift findCC
     cFlags <- coreLift findCFLAGS
     cppFlags <- coreLift findCPPFLAGS

     refcDir <- findDataFile "refc"
     cDir <- findDataFile "c"

     directives <- getDirectives RefC
     let debugFlag = if elem "debug" directives then ["-g"] else []
     let libraryFlag = if asLibrary then ["-fpic"] else []
     crossFlags <- crossCompileFlags directives
     noGmp     <- coreLift $ needsNoGmp     directives
     noThreads <- coreLift $ needsNoThreads directives
     let noGmpFlag     = if noGmp     then ["-DIDRIS2_NO_GMP"]     else []
     let noThreadsFlag = if noThreads then ["-DIDRIS2_NO_THREADS"] else []

     let runccobj = (escapeCmd $
         [cc, "-Werror", "-c"] ++ debugFlag ++ libraryFlag ++ crossFlags
              ++ noGmpFlag ++ noThreadsFlag
              ++ [sourceFile,
                  "-o", objectFile,
                  "-I" ++ refcDir,
                  "-I" ++ cDir])
              ++ " " ++ cppFlags ++ " " ++ cFlags


     log "compiler.refc.cc" 10 runccobj
     0 <- coreLift $ system runccobj
       | _ => pure Nothing

     pure (Just objectFile)

export
compileCFile : {auto c : Ref Ctxt Defs}
            -> {default False asShared : Bool}
            -> (objectFile : String)
            -> (outFile : String)
            -> Core (Maybe String)
compileCFile {asShared} objectFile outFile =
  do cc <- coreLift findCC
     cFlags <- coreLift findCFLAGS
     ldFlags <- coreLift findLDFLAGS
     ldLibs <- coreLift findLDLIBS

     dirs <- getDirs
     directives <- getDirectives RefC
     refcLibDir  <- findRefcLibDir directives
     supportFile <- findSupportLib directives

     let debugFlag = if elem "debug" directives then ["-g"] else []
     let sharedFlag = if asShared then ["-shared"] else []
     crossFlags <- crossCompileFlags directives
     noGmp <- coreLift $ needsNoGmp directives
     noFfi <- coreLift $ needsNoFfi directives
     let gmpLib = if noGmp then [] else ["-lgmp"]
     let ffiLib = if noFfi then [] else ["-lffi"]

     let runcc = (escapeCmd $
         [cc, "-Werror"] ++ debugFlag ++ sharedFlag ++ crossFlags ++ [objectFile,
              "-o", outFile,
              supportFile,
              "-lidris2_refc",
              "-L" ++ refcLibDir
              ] ++ clibdirs (lib_dirs dirs) ++ ["-lm"]
                ++ gmpLib ++ ffiLib)
              ++ " " ++ (unwords [cFlags, ldFlags, ldLibs])

     log "compiler.refc.cc" 10 runcc
     0 <- coreLift $ system runcc
       | _ => pure Nothing

     pure (Just outFile)

||| Link several pre-compiled object files into a single executable.
||| Used by the incremental compilation path, where each module has
||| already been compiled to a `.o` and we just need to stitch them
||| together with the support libraries.
export
compileCFileInc : {auto c : Ref Ctxt Defs}
               -> (objectFiles : List String)
               -> (outFile : String)
               -> Core (Maybe String)
compileCFileInc [] _ = pure Nothing
compileCFileInc objectFiles outFile =
  do cc <- coreLift findCC
     cFlags <- coreLift findCFLAGS
     ldFlags <- coreLift findLDFLAGS
     ldLibs <- coreLift findLDLIBS

     dirs <- getDirs
     directives <- getDirectives RefC
     refcLibDir  <- findRefcLibDir directives
     supportFile <- findSupportLib directives

     let debugFlag = if elem "debug" directives then ["-g"] else []
     crossFlags <- crossCompileFlags directives
     noGmp <- coreLift $ needsNoGmp directives
     noFfi <- coreLift $ needsNoFfi directives
     let gmpLib = if noGmp then [] else ["-lgmp"]
     let ffiLib = if noFfi then [] else ["-lffi"]

     let runcc = (escapeCmd $
         [cc, "-Werror"] ++ debugFlag ++ crossFlags ++ objectFiles ++
              ["-o", outFile,
              supportFile,
              "-lidris2_refc",
              "-L" ++ refcLibDir
              ] ++ clibdirs (lib_dirs dirs) ++ ["-lm"]
                ++ gmpLib ++ ffiLib)
              ++ " " ++ (unwords [cFlags, ldFlags, ldLibs])

     log "compiler.refc.cc" 10 runcc
     0 <- coreLift $ system runcc
       | _ => pure Nothing

     pure (Just outFile)
