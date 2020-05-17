module Idris.CommandLine

import IdrisPaths

import Idris.Version

import Data.List
import Data.Maybe
import Data.Strings

import System

%default total

public export
data PkgCommand
      = Build
      | Install
      | Clean
      | REPL

export
Show PkgCommand where
  show Build = "--build"
  show Install = "--install"
  show Clean = "--clean"
  show REPL = "--repl"

public export
data DirCommand
      = LibDir -- show top level package directory

export
Show DirCommand where
  show LibDir = "--libdir"

||| CLOpt - possible command line options
public export
data CLOpt
  =
   ||| Only typecheck the given file
  CheckOnly |
   ||| The output file from the code generator
  OutputFile String |
   ||| Execute a given function after checking the source file
  ExecFn String |
   ||| Use a specific code generator (default chez)
  SetCG String |
   ||| Don't implicitly import Prelude
  NoPrelude |
   ||| Show the installation prefix
  ShowPrefix |
   ||| Display Idris version
  Version |
   ||| Display help text
  Help |
   ||| Suppress the banner
  NoBanner |
   ||| Run Idris 2 in quiet mode
  Quiet |
   ||| Run Idris 2 in verbose mode (cancels quiet if it's the default)
  Verbose |
   ||| Add a package as a dependency
  PkgPath String |
   ||| Build or install a given package, depending on PkgCommand
  Package PkgCommand String |
   ||| Show locations of data/library directories
  Directory DirCommand |
   ||| The input Idris file
  InputFile String |
   ||| Whether or not to run in IdeMode (easily parsable for other tools)
  IdeMode |
   ||| Whether or not to run IdeMode (using a socket instead of stdin/stdout)
  IdeModeSocket String |
   ||| Run as a checker for the core language TTImp
  Yaffle String |
   ||| Dump metadata from a .ttm file
  Metadata String |
   ||| Dump cases before compiling
  DumpCases String |
   ||| Dump lambda lifted defs before compiling
  DumpLifted String |
   ||| Dump ANF defs before compiling
  DumpANF String |
   ||| Dump VM code defs before compiling
  DumpVMCode String |
   ||| Run a REPL command then exit immediately
  RunREPL String |
  FindIPKG |
  Timing |
  DebugElabCheck |
  BlodwenPaths


ActType : List String -> Type
ActType [] = List CLOpt
ActType (a :: as) = String -> ActType as

record OptDesc where
  constructor MkOpt
  flags : List String
  argdescs : List String
  action : ActType argdescs
  help : Maybe String

options : List OptDesc
options = [MkOpt ["--check", "-c"] [] [CheckOnly]
              (Just "Exit after checking source file"),
           MkOpt ["--output", "-o"] ["file"] (\f => [OutputFile f, Quiet])
              (Just "Specify output file"),
           MkOpt ["--exec", "-x"] ["name"] (\f => [ExecFn f, Quiet])
              (Just "Execute function after checking source file"),
           MkOpt ["--no-prelude"] [] [NoPrelude]
              (Just "Don't implicitly import Prelude"),
           MkOpt ["--codegen", "--cg"] ["backend"] (\f => [SetCG f])
              (Just "Set code generator (default chez)"),
           MkOpt ["--package", "-p"] ["package"] (\f => [PkgPath f])
              (Just "Add a package as a dependency"),

           MkOpt ["--ide-mode"] [] [IdeMode]
              (Just "Run the REPL with machine-readable syntax"),

           MkOpt ["--ide-mode-socket"] [] [IdeModeSocket "localhost:38398"]
              (Just "Run the ide socket mode on default host and port (localhost:38398)"),

           MkOpt ["--ide-mode-socket-with"] ["host:port"] (\hp => [IdeModeSocket hp])
              (Just "Run the ide socket mode on given host and port"),

           MkOpt ["--prefix"] [] [ShowPrefix]
              (Just "Show installation prefix"),
           MkOpt ["--paths"] [] [BlodwenPaths]
              (Just "Show paths"),
           MkOpt ["--build"] ["package file"] (\f => [Package Build f])
              (Just "Build modules/executable for the given package"),
           MkOpt ["--install"] ["package file"] (\f => [Package Install f])
              (Just "Install the given package"),
           MkOpt ["--clean"] ["package file"] (\f => [Package Clean f])
              (Just "Clean intermediate files/executables for the given package"),

           MkOpt ["--libdir"] [] [Directory LibDir]
              (Just "Show library directory"),
           MkOpt ["--no-banner"] [] [NoBanner]
              (Just "Suppress the banner"),
           MkOpt ["--quiet", "-q"] [] [Quiet]
              (Just "Quiet mode; display fewer messages"),
           MkOpt ["--verbose"] [] [Verbose]
              (Just "Verbose mode (default)"),
           MkOpt ["--version", "-v"] [] [Version]
              (Just "Display version string"),
           MkOpt ["--help", "-h", "-?"] [] [Help]
              (Just "Display help text"),
           MkOpt ["--timing"] [] [Timing]
              (Just "Display timing logs"),
           MkOpt ["--find-ipkg"] [] [FindIPKG]
              (Just "Find and use an .ipkg file in a parent directory"),
           MkOpt ["--client"] ["REPL command"] (\f => [RunREPL f])
              (Just "Run a REPL command then quit immediately"),
           -- Internal debugging options
           MkOpt ["--yaffle", "--ttimp"] ["ttimp file"] (\f => [Yaffle f])
              Nothing, -- run ttimp REPL rather than full Idris
           MkOpt ["--ttm" ] ["ttimp file"] (\f => [Metadata f])
              Nothing, -- dump metadata information from the given ttm file
           MkOpt ["--dumpcases"] ["output file"] (\f => [DumpCases f])
              Nothing, -- dump case trees to the given file
           MkOpt ["--dumplifted"] ["output file"] (\f => [DumpLifted f])
              Nothing, -- dump lambda lifted trees to the given file
           MkOpt ["--dumpanf"] ["output file"] (\f => [DumpANF f])
              Nothing, -- dump ANF to the given file
           MkOpt ["--dumpvmcode"] ["output file"] (\f => [DumpVMCode f])
              Nothing, -- dump VM Code to the given file
           MkOpt ["--debug-elab-check"] [] [DebugElabCheck]
              Nothing -- do more elaborator checks (currently conversion in LinearCheck)
           ]

optUsage : OptDesc -> String
optUsage d
    = maybe "" -- Don't show anything if there's no help string (that means
               -- it's an internal option)
        (\h => "  " ++
            let optshow = showSep "," (flags d) ++ " " ++
                    showSep " " (map (\x => "<" ++ x ++ ">") (argdescs d)) in
                optshow ++ pack (List.replicate (minus 26 (length optshow)) ' ')
                ++ h ++ "\n") (help d)
  where
    showSep : String -> List String -> String
    showSep sep [] = ""
    showSep sep [x] = x
    showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
versionMsg : String
versionMsg = "Idris 2, version " ++ showVersion True version

export
usage : String
usage = versionMsg ++ "\n" ++
        "Usage: idris2 [options] [input file]\n\n" ++
        "Available options:\n" ++
        concatMap optUsage options

processArgs : String -> (args : List String) -> List String -> ActType args ->
              Either String (List CLOpt, List String)
processArgs flag [] xs f = Right (f, xs)
processArgs flag (a :: as) [] f
    = Left $ "Missing argument <" ++ a ++ "> for flag " ++ flag
processArgs flag (a :: as) (x :: xs) f
    = processArgs flag as xs (f x)

matchFlag : (d : OptDesc) -> List String ->
            Either String (Maybe (List CLOpt, List String))
matchFlag d [] = Right Nothing -- Nothing left to match
matchFlag d (x :: xs)
    = if x `elem` flags d
         then do args <- processArgs x (argdescs d) xs (action d)
                 Right (Just args)
         else Right Nothing

findMatch : List OptDesc -> List String ->
            Either String (List CLOpt, List String)
findMatch [] [] = Right ([], [])
findMatch [] (f :: args) = Right ([InputFile f], args)
findMatch (d :: ds) args
    = case !(matchFlag d args) of
           Nothing => findMatch ds args
           Just res => Right res

parseOpts : List OptDesc -> List String -> Either String (List CLOpt)
parseOpts opts [] = Right []
parseOpts opts args
   = do (cl, rest) <- findMatch opts args
        cls <- assert_total (parseOpts opts rest) -- 'rest' smaller than 'args'
        pure (cl ++ cls)

export
getOpts : List String -> Either String (List CLOpt)
getOpts opts = parseOpts options opts


export covering
getCmdOpts : IO (Either String (List CLOpt))
getCmdOpts = do (_ :: opts) <- getArgs
                    | _ => pure (Left "Invalid command line")
                pure $ getOpts opts

portPart : String -> Maybe String
portPart p = if p == ""
                then Nothing
                else Just $ assert_total $ prim__strTail p

||| Extract the host and port to bind the IDE socket to
public export
ideSocketModeHostPort : List CLOpt -> (String, Int)
ideSocketModeHostPort []  = ("localhost", 38398)
ideSocketModeHostPort (IdeModeSocket hp :: _) =
  let (h, p) = Strings.break (== ':') hp
      port = fromMaybe 38398 (portPart p >>= parsePositive)
      host = if h == "" then "localhost" else h
  in (host, port)
ideSocketModeHostPort (_ :: rest) = ideSocketModeHostPort rest
