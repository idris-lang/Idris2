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

     let runccobj = (escapeCmd $
         [cc, "-Werror", "-c"] ++ debugFlag ++ libraryFlag ++ crossFlags ++ [sourceFile,
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
     refcDir <- findDataFile "refc"
     supportFile <- findLibraryFile "libidris2_support.a"

     directives <- getDirectives RefC
     let debugFlag = if elem "debug" directives then ["-g"] else []
     let sharedFlag = if asShared then ["-shared"] else []
     crossFlags <- crossCompileFlags directives

     let runcc = (escapeCmd $
         [cc, "-Werror"] ++ debugFlag ++ sharedFlag ++ crossFlags ++ [objectFile,
              "-o", outFile,
              supportFile,
              "-lidris2_refc",
              "-L" ++ refcDir
              ] ++ clibdirs (lib_dirs dirs) ++ [
              "-lgmp", "-lm", "-lffi"])
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
     refcDir <- findDataFile "refc"
     supportFile <- findLibraryFile "libidris2_support.a"

     directives <- getDirectives RefC
     let debugFlag = if elem "debug" directives then ["-g"] else []
     crossFlags <- crossCompileFlags directives

     let runcc = (escapeCmd $
         [cc, "-Werror"] ++ debugFlag ++ crossFlags ++ objectFiles ++
              ["-o", outFile,
              supportFile,
              "-lidris2_refc",
              "-L" ++ refcDir
              ] ++ clibdirs (lib_dirs dirs) ++ [
              "-lgmp", "-lm", "-lffi"])
              ++ " " ++ (unwords [cFlags, ldFlags, ldLibs])

     log "compiler.refc.cc" 10 runcc
     0 <- coreLift $ system runcc
       | _ => pure Nothing

     pure (Just outFile)
