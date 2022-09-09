module Idris.Env

--- All environment variables accessed by the compiler are enumerated in this module.

import public Data.List
import public Data.Maybe

import System

%default total

||| Environment variable used by Idris2 compiler
public export
record EnvDesc where
  constructor MkEnvDesc
  name : String
  help : String

||| All environment variables used by Idris2 compiler
public export
envs : List EnvDesc
envs = [
    MkEnvDesc "EDITOR"               "Editor used in REPL :e command.",
    MkEnvDesc "IDRIS2_PREFIX"        "Idris2 installation prefix.",
    MkEnvDesc "IDRIS2_PATH"          "Directories where Idris2 looks for import files.",
    MkEnvDesc "IDRIS2_PACKAGE_PATH"  "Directories where Idris2 looks for Idris 2 packages.",
    MkEnvDesc "IDRIS2_DATA"          "Directories where Idris2 looks for data files.",
    MkEnvDesc "IDRIS2_LIBS"          "Directories where Idris2 looks for libraries (for code generation).",
    MkEnvDesc "IDRIS2_CG"            "Codegen backend.",
    MkEnvDesc "IDRIS2_INC_CGS"       "Code generators to use (comma separated) when compiling modules incrementally.",
    MkEnvDesc "CHEZ"                 "Chez backend: chez executable.",
    MkEnvDesc "RACKET"               "Racket backend: racket executable.",
    MkEnvDesc "RACKET_RACO"          "Racket backend: raco executable.",
    MkEnvDesc "GAMBIT_GSI"           "Gambit backend: gsi executable.",
    MkEnvDesc "GAMBIT_GSC"           "Gambit backend: gsc executable.",
    MkEnvDesc "GAMBIT_GSC_BACKEND"   "Gambit backend: arguments passed to gsc.",
    MkEnvDesc "IDRIS2_CC"            "RefC backend: C compiler executable.",
    MkEnvDesc "IDRIS2_CFLAGS"        "RefC backend: C compiler flags.",
    MkEnvDesc "IDRIS2_CPPFLAGS"      "RefC backend: C preprocessor flags.",
    MkEnvDesc "IDRIS2_LDFLAGS"       "RefC backend: C linker flags.",
    MkEnvDesc "CC"                   "RefC backend: C compiler executable (IDRIS2_CC takes precedence).",
    MkEnvDesc "CFLAGS"               "RefC backend: C compiler flags (IDRIS2_CFLAGS takes precedence).",
    MkEnvDesc "CPPFLAGS"             "RefC backend: C preprocessor flags (IDRIS2_CPPFLAGS takes precedence).",
    MkEnvDesc "LDFLAGS"              "RefC backend: C linker flags (IDRIS2_LDFLAGS takes precedence).",
    MkEnvDesc "NODE"                 "NodeJS backend: NodeJS executable.",
    MkEnvDesc "PATH"                 "PATH variable is used to search for executables in certain codegens."]

--- `public export` only for `auto` to work in `idrisGetEnv`
public export
envNames : List String
envNames = map (.name) envs

||| Query documented environment variable
public export
idrisGetEnv : HasIO io => (name : String) ->
  {auto known : IsJust (find (name ==) Env.envNames)}
  -> io (Maybe String)
idrisGetEnv name = getEnv name
