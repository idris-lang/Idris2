module Compiler.RefC.CC

import Core.Context
import Core.Context.Log
import Core.Options
import Core.Directory

import System

%default total

findCC : IO String
findCC
    = do Nothing <- getEnv "IDRIS2_CC"
           | Just cc => pure cc
         Nothing <- getEnv "CC"
           | Just cc => pure cc
         pure "cc"

findCFLAGS : IO String
findCFLAGS
  = do Nothing <- getEnv "IDRIS2_CFLAGS"
         | Just cflags => pure cflags
       Nothing <- getEnv "CFLAGS"
         | Just cflags => pure cflags
       pure ""

findCPPFLAGS : IO String
findCPPFLAGS
  = do Nothing <- getEnv "IDRIS2_CPPFLAGS"
         | Just cppflags => pure cppflags
       Nothing <- getEnv "CPPFLAGS"
         | Just cppflags => pure cppflags
       pure ""

findLDFLAGS : IO String
findLDFLAGS
  = do Nothing <- getEnv "IDRIS2_LDFLAGS"
         | Just ldflags => pure ldflags
       Nothing <- getEnv "LDFLAGS"
         | Just ldflags => pure ldflags
       pure ""

clibdirs : List String -> List String
clibdirs ds = map (\d => "-L" ++ d) ds

-- cincdirs : List String -> String
-- cincdirs ds = concat (map (\d => "-I" ++ d ++ " ") ds)

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

     let libraryFlag = if asLibrary then ["-fpic"] else []

     let runccobj = escapeCmd $
         [cc, "-Werror", "-c"] ++ libraryFlag ++ [sourceFile,
              "-o", objectFile,
              "-I" ++ refcDir,
              "-I" ++ cDir]

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

     dirs <- getDirs
     refcDir <- findDataFile "refc"
     supportFile <- findLibraryFile "libidris2_support.a"

     let sharedFlag = if asShared then ["-shared"] else []

     let runcc = escapeCmd $
         [cc, "-Werror"] ++ sharedFlag ++ [objectFile,
              "-o", outFile,
              supportFile,
              "-lidris2_refc",
              "-L" ++ refcDir
              ] ++ clibdirs (lib_dirs dirs) ++ [
              "-lgmp", "-lm"]

     log "compiler.refc.cc" 10 runcc
     0 <- coreLift $ system runcc
       | _ => pure Nothing

     pure (Just outFile)
