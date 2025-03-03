module Core.Options

import Core.Core
import Core.Name
import public Core.Options.Log
import Core.TT

import Libraries.Utils.Path
import Idris.Syntax.Pragmas

import Data.List
import Data.Maybe
import Data.String

%default total

public export
record Dirs where
  constructor MkDirs
  working_dir : String
  source_dir : Maybe String -- source directory, relative to working directory
  build_dir : String -- build directory, relative to working directory
  depends_dir : String -- local dependencies directory, relative to working directory
  output_dir : Maybe String -- output directory, relative to working directory
  prefix_dir : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files
  package_search_paths : List Path -- paths at which to look for packages
  package_dirs : List String -- places where specific needed packages at required versions are located
  lib_dirs : List String -- places to look for libraries (for code generation)
  data_dirs : List String -- places to look for data file

export
execBuildDir : Dirs -> String
execBuildDir d = build_dir d </> "exec"

export
outputDirWithDefault : Dirs -> String
outputDirWithDefault d = fromMaybe (build_dir d </> "exec") (output_dir d)

public export
toString : Dirs -> String
toString d@(MkDirs wdir sdir bdir ldir odir dfix edirs ppaths pdirs ldirs ddirs) = """
  + Working Directory      :: \{ show wdir }
  + Source Directory       :: \{ show sdir }
  + Build Directory        :: \{ show bdir }
  + Local Depend Directory :: \{ show ldir }
  + Output Directory       :: \{ show $ outputDirWithDefault d }
  + Installation Prefix    :: \{ show dfix }
  + Extra Directories      :: \{ show edirs }
  + Package Search Paths   :: \{ show ppaths }
  + Package Directories    :: \{ show pdirs }
  + CG Library Directories :: \{ show ldirs }
  + Data Directories       :: \{ show ddirs }
  """

public export
data CG = Chez
        | ChezSep
        | Racket
        | Gambit
        | Node
        | Javascript
        | RefC
        | VMCodeInterp
        | Other String

export
Eq CG where
  Chez == Chez = True
  ChezSep == ChezSep = True
  Racket == Racket = True
  Gambit == Gambit = True
  Node == Node = True
  Javascript == Javascript = True
  RefC == RefC = True
  VMCodeInterp == VMCodeInterp = True
  Other s == Other t = s == t
  _ == _ = False

export
Show CG where
  show Chez = "chez"
  show ChezSep = "chez-sep"
  show Racket = "racket"
  show Gambit = "gambit"
  show Node = "node"
  show Javascript = "javascript"
  show RefC = "refc"
  show VMCodeInterp = "vmcode-interp"
  show (Other s) = s

public export
record PairNames where
  constructor MkPairNs
  pairType : Name
  fstName : Name
  sndName : Name

public export
record RewriteNames where
  constructor MkRewriteNs
  equalType : Name
  rewriteName : Name

public export
record PrimNames where
  constructor MkPrimNs
  fromIntegerName : Maybe Name
  fromStringName : Maybe Name
  fromCharName : Maybe Name
  fromDoubleName : Maybe Name
  fromTTImpName : Maybe Name
  fromNameName : Maybe Name
  fromDeclsName : Maybe Name

export
primNamesToList : PrimNames -> List Name
primNamesToList (MkPrimNs i s c d t n dl) = catMaybes [i,s,c,d,t,n,dl]

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record ElabDirectives where
  constructor MkElabDirectives
  lazyActive : Bool
  unboundImplicits : Bool
  totality : TotalReq
  ambigLimit : Nat
  autoImplicitLimit : Nat
  nfThreshold : Nat
  totalLimit : Nat
  --
  -- produce traditional (prefix) record projections,
  -- in addition to postfix (dot) projections
  -- default: yes
  prefixRecordProjections : Bool

public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
  totalReq : TotalReq
  nobanner : Bool
  findipkg : Bool
  codegen : CG
  directives : List String
  searchTimeout : Integer -- maximum number of milliseconds to run
                          -- expression/program search
  ignoreMissingPkg : Bool -- fail silently on missing packages. This is because
          -- while we're bootstrapping, we find modules by a different route
          -- but we still want to have the dependencies listed properly

  -- Troubleshooting
  logEnabled : Bool -- do we check logging flags at all? This is 'False' until
                    -- any logging is enabled.
  logLevel : LogLevels
  logTimings : Maybe Nat -- log level, higher means more details
  logTreeEnabled : Bool -- do we show logs in a tree-like output
  logDepth : Nat -- depth level of logging to separate related stuff visually
  debugElabCheck : Bool -- do conversion check to verify results of elaborator
  dumpcases : Maybe String -- file to output compiled case trees
  dumplifted : Maybe String -- file to output lambda lifted definitions
  dumpanf : Maybe String -- file to output ANF definitions
  dumpvmcode : Maybe String -- file to output VM code definitions
  profile : Bool -- generate profiling information, if supported
  logErrorCount : Nat -- when parsing alternatives fails, how many errors
                      -- should be shown.
  noCSE : Bool -- disable common subexpression elimination

  -- Warnings
  warningsAsErrors : Bool
  showShadowingWarning : Bool

  -- Experimental
  checkHashesInsteadOfModTime : Bool
  incrementalCGs : List CG
  wholeProgram : Bool
     -- Use whole program compilation for executables, no matter what
     -- incremental CGs are set (intended for overriding any environment
     -- variables that set incremental compilation)
  caseTreeHeuristics : Bool -- apply heuristics to pick matches for case tree building

public export
record PPrinter where
  constructor MkPPOpts
  showImplicits : Bool
  showMachineNames : Bool
  showFullEnv : Bool
  fullNamespace : Bool

public export
record Options where
  constructor MkOptions
  dirs : Dirs
  printing : PPrinter
  session : Session
  elabDirectives : ElabDirectives
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  extensions : List LangExt
  additionalCGs : List (String, CG)
  hashFn : Maybe String
  -- fullName and definition for %foreign_impl
  foreignImpl : List (Name, String)

export
availableCGs : Options -> List (String, CG)
availableCGs o
    = [("chez", Chez),
       ("chez-sep", ChezSep),
       ("racket", Racket),
       ("node", Node),
       ("javascript", Javascript),
       ("refc", RefC),
       ("gambit", Gambit),
       ("vmcode-interp", VMCodeInterp)] ++ additionalCGs o

export
getCG : Options -> String -> Maybe CG
getCG o cg = lookup (toLower cg) (availableCGs o)

defaultDirs : Dirs
defaultDirs = MkDirs "." Nothing "build" "depends" Nothing
                     "/usr/local" ["."] [] [] [] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False False True False

export
defaultSession : Session
defaultSession = MkSessionOpts False CoveringOnly False False Chez [] 1000 False False
                               defaultLogLevel Nothing False 0 False Nothing Nothing
                               Nothing Nothing False 1 False False True
                               False [] False False

export
defaultElab : ElabDirectives
defaultElab = MkElabDirectives True True CoveringOnly 3 50 25 5 True

-- FIXME: This turns out not to be reliably portable, since different systems
-- may have tools with the same name but different required arugments. We
-- probably need another way (perhaps our own internal hash function, although
-- that's not going to be as good as sha256).
export
defaultHashFn : Core (Maybe String)
defaultHashFn
    = do Nothing <- coreLift $ pathLookup ["sha256sum", "gsha256sum"]
           | Just p => pure $ Just $ p ++ " --tag"
         Nothing <- coreLift $ pathLookup ["sha256"]
           | Just p => pure $ Just p
         Nothing <- coreLift $ pathLookup ["openssl"]
           | Just p => pure $ Just $ p ++ " sha256"
         pure Nothing

export
defaults : Core Options
defaults
    = do -- hashFn <- defaultHashFn
         -- Temporarily disabling the hash function until we have a more
         -- portable way of working out what to call, and allowing a way for
         -- it to fail gracefully.
         pure $ MkOptions
           defaultDirs defaultPPrint defaultSession defaultElab Nothing Nothing
           (MkPrimNs Nothing Nothing Nothing Nothing Nothing Nothing Nothing) [] [] Nothing []

-- Reset the options which are set by source files
export
clearNames : Options -> Options
clearNames = { pairnames := Nothing,
               rewritenames := Nothing,
               primnames := MkPrimNs Nothing Nothing Nothing Nothing Nothing Nothing Nothing,
               foreignImpl := [],
               extensions := []
             }

export
addForeignImpl : (fullName : Name) -> (def : String) -> Options -> Options
addForeignImpl fullName def = { foreignImpl $= ((fullName, def) ::) }

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = { pairnames := Just (MkPairNs ty f s) }

export
setRewrite : (eq : Name) -> (rwlemma : Name) -> Options -> Options
setRewrite eq rw = { rewritenames := Just (MkRewriteNs eq rw) }

export
setFromInteger : Name -> Options -> Options
setFromInteger n = { primnames->fromIntegerName := Just n }

export
setFromString : Name -> Options -> Options
setFromString n = { primnames->fromStringName := Just n }

export
setFromChar : Name -> Options -> Options
setFromChar n = { primnames->fromCharName := Just n }

export
setFromDouble : Name -> Options -> Options
setFromDouble n = { primnames->fromDoubleName := Just n }

export
setFromTTImp : Name -> Options -> Options
setFromTTImp n = { primnames->fromTTImpName := Just n }

export
setFromName : Name -> Options -> Options
setFromName n = { primnames->fromNameName := Just n }

export
setFromDecls : Name -> Options -> Options
setFromDecls n = { primnames->fromDeclsName := Just n }

export
setExtension : LangExt -> Options -> Options
setExtension e = { extensions $= (e ::) }

export
isExtension : LangExt -> Options -> Bool
isExtension e opts = e `elem` extensions opts

export
addCG : (String, CG) -> Options -> Options
addCG cg = { additionalCGs $= (cg::) }
