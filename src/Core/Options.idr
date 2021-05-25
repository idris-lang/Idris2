module Core.Options

import Core.Core
import Core.Name
import public Core.Options.Log
import Core.TT
import Libraries.Utils.Binary
import Libraries.Utils.Path

import Data.List
import Data.Maybe
import Data.Strings

import System.Info

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
  package_dirs : List String -- places to look for packages
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
toString d@(MkDirs wdir sdir bdir ldir odir dfix edirs pdirs ldirs ddirs) =
  unlines [ "+ Working Directory      :: " ++ show wdir
          , "+ Source Directory       :: " ++ show sdir
          , "+ Build Directory        :: " ++ show bdir
          , "+ Local Depend Directory :: " ++ show ldir
          , "+ Output Directory       :: " ++ show (outputDirWithDefault d)
          , "+ Installation Prefix    :: " ++ show dfix
          , "+ Extra Directories      :: " ++ show edirs
          , "+ Package Directories    :: " ++ show pdirs
          , "+ CG Library Directories :: " ++ show ldirs
          , "+ Data Directories       :: " ++ show ddirs]

public export
data CG = Chez
        | ChezSep
        | Racket
        | Gambit
        | Node
        | Javascript
        | RefC
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

export
primNamesToList : PrimNames -> List Name
primNamesToList (MkPrimNs i s c d) = catMaybes [i,s,c,d]

public export
data LangExt
     = ElabReflection
     | Borrowing -- not yet implemented

export
Eq LangExt where
  ElabReflection == ElabReflection = True
  Borrowing == Borrowing = True
  _ == _ = False

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
  --
  -- produce traditional (prefix) record projections,
  -- in addition to postfix (dot) projections
  -- default: yes
  prefixRecordProjections : Bool

public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
  nobanner : Bool
  findipkg : Bool
  codegen : CG
  directives : List String
  logEnabled : Bool -- do we check logging flags at all? This is 'False' until
                    -- any logging is enabled.
  logLevel : LogLevels
  logTimings : Bool
  ignoreMissingPkg : Bool -- fail silently on missing packages. This is because
          -- while we're bootstrapping, we find modules by a different route
          -- but we still want to have the dependencies listed properly
  debugElabCheck : Bool -- do conversion check to verify results of elaborator
  dumpcases : Maybe String -- file to output compiled case trees
  dumplifted : Maybe String -- file to output lambda lifted definitions
  dumpanf : Maybe String -- file to output ANF definitions
  dumpvmcode : Maybe String -- file to output VM code definitions
  profile : Bool -- generate profiling information, if supported
  -- Warnings
  warningsAsErrors : Bool
  showShadowingWarning : Bool

public export
record PPrinter where
  constructor MkPPOpts
  showImplicits : Bool
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


export
availableCGs : Options -> List (String, CG)
availableCGs o
    = [("chez", Chez),
       ("chez-sep", ChezSep),
       ("racket", Racket),
       ("node", Node),
       ("javascript", Javascript),
       ("refc", RefC),
       ("gambit", Gambit)] ++ additionalCGs o

export
getCG : Options -> String -> Maybe CG
getCG o cg = lookup (toLower cg) (availableCGs o)

defaultDirs : Dirs
defaultDirs = MkDirs "." Nothing "build" "depends" Nothing
                     "/usr/local" ["."] [] [] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False True False

export
defaultSession : Session
defaultSession = MkSessionOpts False False False Chez [] False defaultLogLevel
                               False False False Nothing Nothing
                               Nothing Nothing False False True

export
defaultElab : ElabDirectives
defaultElab = MkElabDirectives True True CoveringOnly 3 50 50 True

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession
                     defaultElab Nothing Nothing
                     (MkPrimNs Nothing Nothing Nothing Nothing) []
                     []

-- Reset the options which are set by source files
export
clearNames : Options -> Options
clearNames = record { pairnames = Nothing,
                      rewritenames = Nothing,
                      primnames = MkPrimNs Nothing Nothing Nothing Nothing,
                      extensions = []
                    }

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = record { pairnames = Just (MkPairNs ty f s) }

export
setRewrite : (eq : Name) -> (rwlemma : Name) -> Options -> Options
setRewrite eq rw = record { rewritenames = Just (MkRewriteNs eq rw) }

export
setFromInteger : Name -> Options -> Options
setFromInteger n = record { primnames->fromIntegerName = Just n }

export
setFromString : Name -> Options -> Options
setFromString n = record { primnames->fromStringName = Just n }

export
setFromChar : Name -> Options -> Options
setFromChar n = record { primnames->fromCharName = Just n }

export
setFromDouble : Name -> Options -> Options
setFromDouble n = record { primnames->fromDoubleName = Just n }

export
setExtension : LangExt -> Options -> Options
setExtension e = record { extensions $= (e ::) }

export
isExtension : LangExt -> Options -> Bool
isExtension e opts = e `elem` extensions opts

export
addCG : (String, CG) -> Options -> Options
addCG cg = record { additionalCGs $= (cg::) }
