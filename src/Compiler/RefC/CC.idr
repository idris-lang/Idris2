module Compiler.RefC.CC

import Core.Context
import Core.Context.Log
import Core.Options

import System

import Idris.Version
import Libraries.Utils.Path

findCC : IO String
findCC
    = do Nothing <- getEnv "IDRIS2_CC"
           | Just cc => pure cc
         Nothing <- getEnv "CC"
           | Just cc => pure cc
         pure "cc"

fullprefix_dir : Dirs -> String -> String
fullprefix_dir dirs sub
    = prefix_dir dirs </> "idris2-" ++ showVersion False version </> sub

export
compileCObjectFile : {auto c : Ref Ctxt Defs}
                  -> {default False asLibrary : Bool}
                  -> (sourceFile : String)
                  -> (objectFile : String)
                  -> Core (Maybe String)
compileCObjectFile {asLibrary} sourceFile objectFile =
  do cc <- coreLift findCC
     dirs <- getDirs

     let libraryFlag = if asLibrary then "-fpic " else ""

     let runccobj = cc ++ " -c " ++ libraryFlag ++ sourceFile ++
                       " -o " ++ objectFile ++ " " ++
                       "-I" ++ fullprefix_dir dirs "refc " ++
                       "-I" ++ fullprefix_dir dirs "include"

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
     dirs <- getDirs

     let sharedFlag = if asShared then "-shared " else ""

     let runcc = cc ++ " " ++ sharedFlag ++ objectFile ++
                       " -o " ++ outFile ++ " " ++
                       fullprefix_dir dirs "lib" </> "libidris2_support.a" ++ " " ++
                       "-lidris2_refc " ++
                       "-L" ++ fullprefix_dir dirs "refc " ++
                       clibdirs (lib_dirs dirs)

     log "compiler.refc.cc" 10 runcc
     0 <- coreLift $ system runcc
       | _ => pure Nothing

     pure (Just outFile)

  where
    clibdirs : List String -> String
    clibdirs ds = concat (map (\d => "-L" ++ d ++ " ") ds)
