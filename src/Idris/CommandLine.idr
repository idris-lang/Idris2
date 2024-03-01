module Idris.CommandLine

import Idris.Env
import Idris.Version

import Core.Options

import Data.List
import Data.Maybe
import Data.String
import Data.Either

import System

%default total

public export
data PkgCommand
      = Build
      | Install
      | InstallWithSrc
      | MkDoc
      | Typecheck
      | Clean
      | REPL
      | Init

export
Show PkgCommand where
  show Build = "--build"
  show Install = "--install"
  show InstallWithSrc = "--install-with-src"
  show MkDoc = "--mkdoc"
  show Typecheck = "--typecheck"
  show Clean = "--clean"
  show REPL = "--repl"
  show Init = "--init"

public export
data DirCommand
      = LibDir | -- show top level package directory
         ||| Show the installation prefix
        Prefix |
        BlodwenPaths

export
Show DirCommand where
  show LibDir = "--libdir"
  show Prefix = "--prefix"
  show BlodwenPaths = "--paths"

||| Help topics
public export
data HelpTopic
  = ||| Interactive debugging topics
    HelpLogging
  | ||| The various pragmas
    HelpPragma

recogniseHelpTopic : String -> Maybe HelpTopic
recogniseHelpTopic "logging"   = pure HelpLogging
recogniseHelpTopic "pragma" = pure HelpPragma
recogniseHelpTopic _ = Nothing

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
   ||| Use a specific code generator
  SetCG String |
   ||| Pass a directive to the code generator
  Directive String |
   ||| Don't implicitly import Prelude
  NoPrelude |
   ||| Set source directory
  SourceDir String |
   ||| Set build directory
  BuildDir String |
   ||| Set output directory
  OutputDir String |
   ||| Generate profile data when compiling (backend dependent)
  Profile |
   ||| Display Idris version
  Version |
   ||| Display the TTC version currently used
  TTCVersion |
   ||| Display help text
  Help (Maybe HelpTopic) |
   ||| Suppress the banner
  NoBanner |
   ||| Run Idris 2 in quiet mode
  Quiet |
   ||| Show machine names when pretty printing
  ShowMachineNames |
   ||| Show namespaces when pretty printing
  ShowNamespaces |
   ||| Run Idris 2 in verbose mode (cancels quiet if it's the default)
  Verbose |
   ||| Set the console width for REPL output
  ConsoleWidth (Maybe Nat) |
   ||| Whether to use color in the console output
  Color Bool |
   ||| Set the log level globally
  Logging LogLevel |
   ||| Add a package as a dependency
  PkgPath String |
   ||| List installed packages
  ListPackages |
   ||| Build or install a given package, depending on PkgCommand
  Package PkgCommand (Maybe String) |
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
  IgnoreMissingIPKG |
  FindIPKG |
  Timing (Maybe Nat) |
  DebugElabCheck |
  AltErrorCount Nat |
   ||| Treat warnings as errors
  WarningsAsErrors |
   ||| Do not print shadowing warnings
  IgnoreShadowingWarnings |
   ||| Use SHA256 hashes to determine if a source file needs rebuilding instead
   ||| of modification time.
  HashesInsteadOfModTime |
   ||| Apply experimental heuristics to case tree generation that
   ||| sometimes improves performance and reduces compiled code
   ||| size.
  CaseTreeHeuristics |
   ||| Use incremental code generation, if the backend supports it
  IncrementalCG String |
   ||| Use whole program compilation - overrides IncrementalCG if set
  WholeProgram |
   ||| Generate bash completion info
  BashCompletion String String |
   ||| Generate bash completion script
  BashCompletionScript String |
   ||| Generate zsh completion script
  ZshCompletionScript String |
   ||| Turn on %default total globally
  Total |
   ||| Disable common subexpression elimination
  NoCSE

||| Extract the host and port to bind the IDE socket to
export
ideSocketModeAddress : List CLOpt -> (String, Int)
ideSocketModeAddress []  = ("localhost", 0)
ideSocketModeAddress (IdeModeSocket hp :: _) =
  let (h, p) = String.break (== ':') hp
      port = fromMaybe 0 (portPart p >>= parsePositive)
      host = if h == "" then "localhost" else h
  in (host, port)
  where
    portPart : String -> Maybe String
    portPart p = if p == ""
                    then Nothing
                    else Just $ assert_total $ prim__strTail p
ideSocketModeAddress (_ :: rest) = ideSocketModeAddress rest

formatSocketAddress : (String, Int) -> String
formatSocketAddress (host, port) = host ++ ":" ++ show port

data OptType
  = Required String
   | Optional String
   | RequiredNat String
   | AutoNat String
   | RequiredLogLevel String

Show OptType where
  show (Required a) = "<" ++ a ++ ">"
  show (RequiredNat a) = "<" ++ a ++ ">"
  show (RequiredLogLevel a) = "<" ++ a ++ ">"
  show (Optional a) = "[" ++ a ++ "]"
  show (AutoNat a) = "<" ++ a ++ ">"

ActType : List OptType -> Type
ActType [] = List CLOpt
ActType (Required a :: as) = String -> ActType as
ActType (RequiredNat a :: as) = Nat -> ActType as
ActType (RequiredLogLevel a :: as) = LogLevel -> ActType as
ActType (Optional a :: as) = Maybe String -> ActType as
ActType (AutoNat a :: as) = Maybe Nat -> ActType as

record OptDesc where
  constructor MkOpt
  flags : List String
  argdescs : List OptType
  action : ActType argdescs
  help : Maybe String

optSeparator : OptDesc
optSeparator = MkOpt [] [] [] Nothing

showDefault : Show a => a -> String
showDefault x = "(default " ++ show x ++ ")"

options : List OptDesc
options = [MkOpt ["--check", "-c"] [] [CheckOnly]
              (Just "Exit after checking source file"),
           MkOpt ["--output", "-o"] [Required "file"] (\f => [OutputFile f, Quiet])
              (Just "Specify output file"),
           MkOpt ["--exec", "-x"] [Required "name"] (\f => [ExecFn f, Quiet])
              (Just "Execute function after checking source file"),
           MkOpt ["--no-prelude"] [] [NoPrelude]
              (Just "Don't implicitly import Prelude"),
           MkOpt ["--codegen", "--cg"] [Required "backend"] (\f => [SetCG f])
              (Just $ "Set code generator " ++ showDefault (codegen defaultSession)),
           MkOpt ["--incremental-cg", "--inc"] [Required "backend"] (\f => [IncrementalCG f])
             (Just "Incremental code generation on given backend"),
           MkOpt ["--whole-program", "--wp"] [] [WholeProgram]
             (Just "Use whole program compilation (overrides --inc)"),
           MkOpt ["--directive"] [Required "directive"] (\d => [Directive d])
              (Just $ "Pass a directive to the current code generator"),
           MkOpt ["--package", "-p"] [Required "package"] (\f => [PkgPath f])
              (Just "Add a package as a dependency"),
           MkOpt ["--source-dir"] [Required "dir"] (\d => [SourceDir d])
              (Just $ "Set source directory"),
           MkOpt ["--build-dir"] [Required "dir"] (\d => [BuildDir d])
              (Just $ "Set build directory"),
           MkOpt ["--output-dir"] [Required "dir"] (\d => [OutputDir d])
              (Just $ "Set output directory"),
           MkOpt ["--profile"] [] [Profile]
              (Just "Generate profile data when compiling, if supported"),
           MkOpt ["--no-cse"] [] [NoCSE]
              (Just "Disable common subexpression elimination"),

           optSeparator,
           MkOpt ["--total"] [] [Total]
              (Just "Require functions to be total by default"),
           MkOpt ["-Werror"] [] [WarningsAsErrors]
              (Just "Treat warnings as errors"),
           MkOpt ["-Wno-shadowing"] [] [IgnoreShadowingWarnings]
              (Just "Do not print shadowing warnings"),

           optSeparator,
           MkOpt ["-Xcheck-hashes"] [] [HashesInsteadOfModTime]
             (Just "Use SHA256 hashes instead of modification time to determine if a source file needs rebuilding"),
           MkOpt ["-Xcase-tree-opt"] [] [CaseTreeHeuristics]
              (Just "Apply experimental optimizations to case tree generation"),

           optSeparator,
           MkOpt ["--prefix"] [] [Directory Prefix]
              (Just "Show installation prefix"),
           MkOpt ["--paths"] [] [Directory BlodwenPaths]
              (Just "Show paths"),
           MkOpt ["--libdir"] [] [Directory LibDir]
              (Just "Show library directory"),
           MkOpt ["--list-packages"] [] [ListPackages]
              (Just "List installed packages"),

           optSeparator,
           MkOpt ["--init"] [Optional "package file"]
              (\ f => [Package Init f])
              (Just "Interactively initialise a new project"),
           MkOpt ["--build"] [Optional "package file"]
               (\f => [Package Build f])
              (Just "Build modules/executable for the given package"),
           MkOpt ["--install"] [Optional "package file"]
              (\f => [Package Install f])
              (Just "Install the given package"),
           MkOpt ["--install-with-src"] [Optional "package file"]
              (\f => [Package InstallWithSrc f])
              (Just "Install the given package"),
           MkOpt ["--mkdoc"] [Optional "package file"]
              (\f => [Package MkDoc f])
              (Just "Build documentation for the given package"),
           MkOpt ["--typecheck"] [Optional "package file"]
              (\f => [Package Typecheck f])
              (Just "Typechecks the given package without code generation"),
           MkOpt ["--clean"] [Optional "package file"] (\f => [Package Clean f])
              (Just "Clean intermediate files/executables for the given package"),
           MkOpt ["--repl"] [Optional "package file"] (\f => [Package REPL f])
              (Just "Build the given package and launch a REPL instance."),
           MkOpt ["--find-ipkg"] [] [FindIPKG]
              (Just "Find and use an .ipkg file in a parent directory."),
           MkOpt ["--ignore-missing-ipkg"] [] [IgnoreMissingIPKG]
              (Just "Fail silently if a dependency is missing."),

           optSeparator,
           MkOpt ["--ide-mode"] [] [IdeMode]
              (Just "Run the REPL with machine-readable syntax"),
           MkOpt ["--ide-mode-socket"] [Optional "host:port"]
                 (\hp => [IdeModeSocket $ fromMaybe (formatSocketAddress (ideSocketModeAddress [])) hp])
              (Just $ "Run the ide socket mode on given host and port (random open socket by default)"),

           optSeparator,
           MkOpt ["--client"] [Required "REPL command"] (\f => [RunREPL f])
              (Just "Run a REPL command then quit immediately"),
           MkOpt ["--timing"] [AutoNat "level"] (\ n => [Timing n])
              (Just "Display timing logs"),

           optSeparator,
           MkOpt ["--no-banner"] [] [NoBanner]
              (Just "Suppress the banner"),
           MkOpt ["--quiet", "-q"] [] [Quiet]
              (Just "Quiet mode; display fewer messages"),
           MkOpt ["--console-width"] [AutoNat "console width"] (\l => [ConsoleWidth l])
              (Just "Width for console output (0 for unbounded) (auto by default)"),
           MkOpt ["--show-machine-names"] [] [ShowMachineNames]
              (Just "Show machine names when pretty printing"),
           MkOpt ["--show-namespaces"] [] [ShowNamespaces]
              (Just "Show namespaces when pretty printing"),
           MkOpt ["--color", "--colour"] [] ([Color True])
              (Just "Forces colored console output (enabled by default)"),
           MkOpt ["--no-color", "--no-colour"] [] ([Color False])
              (Just "Disables colored console output"),
           MkOpt ["--verbose"] [] [Verbose]
              (Just "Verbose mode (default)"),
           MkOpt ["--log"] [RequiredLogLevel "log level"] (\l => [Logging l])
              (Just "Global log level (0 by default)"),

           optSeparator,
           MkOpt ["--version", "-v"] [] [Version]
              (Just "Display version string"),
           MkOpt ["--ttc-version"] [] [TTCVersion]
              (Just "Display TTC version string"),
           MkOpt ["--help", "-h", "-?"] [Optional "topic"] (\ tp => [Help (tp >>= recogniseHelpTopic)])
              (Just "Display help text"),

           -- Internal debugging options
           MkOpt ["--yaffle", "--ttimp"] [Required "ttimp file"] (\f => [Yaffle f])
              Nothing, -- run ttimp REPL rather than full Idris
           MkOpt ["--ttm" ] [Required "ttimp file"] (\f => [Metadata f])
              Nothing, -- dump metadata information from the given ttm file
           MkOpt ["--dumpcases"] [Required "output file"] (\f => [DumpCases f])
              Nothing, -- dump case trees to the given file
           MkOpt ["--dumplifted"] [Required "output file"] (\f => [DumpLifted f])
              Nothing, -- dump lambda lifted trees to the given file
           MkOpt ["--dumpanf"] [Required "output file"] (\f => [DumpANF f])
              Nothing, -- dump ANF to the given file
           MkOpt ["--dumpvmcode"] [Required "output file"] (\f => [DumpVMCode f])
              Nothing, -- dump VM Code to the given file
           MkOpt ["--debug-elab-check"] [] [DebugElabCheck]
              Nothing, -- do more elaborator checks (currently conversion in LinearCheck)
           MkOpt ["--alt-error-count"] [RequiredNat "alternative count"] (\c => [AltErrorCount c])
              (Just "Outputs errors for the given number of alternative parsing attempts."),

           optSeparator,
           -- bash completion
           MkOpt ["--bash-completion"]
                 [ Required "input"
                 , Required "previous input"]
                 (\w1,w2 => [BashCompletion w1 w2])
                 (Just "Print bash autocompletion information"),
           MkOpt ["--bash-completion-script"]
                 [ Required "function name" ]
                 (\n => [BashCompletionScript n])
                 (Just "Generate a bash script to activate autocompletion for Idris2"),
           -- zsh completion
           MkOpt ["--zsh-completion-script"]
                 [ Required "function name" ]
                 (\n => [ZshCompletionScript n])
                 (Just "Generate a zsh script (via bashcompinit) to activate autocompletion for Idris2")
           ]

optShow : OptDesc -> (String, Maybe String)
optShow (MkOpt [] _ _ _) = ("", Just "")
optShow (MkOpt flags argdescs action help) = (showSep ", " flags ++ " " ++
                                              showSep " " (map show argdescs),
                                              help)
  where
    showSep : String -> List String -> String
    showSep sep [] = ""
    showSep sep [x] = x
    showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

firstColumnWidth : Nat
firstColumnWidth = let maxOpt = foldr max 0 $ map (length . fst . optShow) options
                       maxEnv = foldr max 0 $ map (length . .name) envs in
                       max maxOpt maxEnv

makeTextFromOptionsOrEnvs : List (String, Maybe String) -> String
makeTextFromOptionsOrEnvs rows = concatMap (optUsage firstColumnWidth) rows
  where
    optUsage : Nat -> (String, Maybe String) -> String
    optUsage maxOpt (optshow, help) = maybe ""  -- Don't show anything if there's no help string (that means
                                                -- it's an internal option)
                                      (\h => "  " ++ optshow ++
                                             pack (List.replicate (minus (maxOpt + 2) (length optshow)) ' ') ++
                                             h ++ "\n")
                                      help

optsUsage : String
optsUsage = makeTextFromOptionsOrEnvs $ map optShow options

envsUsage : String
envsUsage = makeTextFromOptionsOrEnvs $ map (\e => (e.name, Just e.help)) envs

export
versionMsg : String
versionMsg = "Idris 2, version " ++ show version

export
usage : String
usage = """
  \{ versionMsg }
  Usage: idris2 [options] [input file]

  Available options:
  \{ optsUsage }
  Environment variables:
  \{ envsUsage }
  """

checkNat : Integer -> Maybe Nat
checkNat n = toMaybe (n >= 0) (integerToNat n)

processArgs : String -> (args : List OptType) -> List String -> ActType args ->
              Either String (List CLOpt, List String)
processArgs flag [] xs f = Right (f, xs)
-- Missing required arguments
processArgs flag (opt@(Required _) :: as) [] f =
  Left $ "Missing required argument " ++ show opt ++ " for flag " ++ flag
processArgs flag (opt@(RequiredNat _) :: as) [] f =
  Left $ "Missing required argument " ++ show opt ++ " for flag " ++ flag
processArgs flag (opt@(RequiredLogLevel _) :: as) [] f =
  Left $ "Missing required argument " ++ show opt ++ " for flag " ++ flag
processArgs flag (Optional a :: as) [] f =
  processArgs flag as [] (f Nothing)
processArgs flag (opt@(AutoNat _) :: as) [] f =
  Left $ "Missing required argument " ++ show opt ++ " for flag " ++ flag
-- Happy cases
processArgs flag (RequiredNat a :: as) (x :: xs) f =
  do arg <- maybeToEither ("Expected Nat argument " ++ show x ++ " for flag " ++ flag)
                          (parseInteger x >>= checkNat)
     processArgs flag as xs (f arg)
processArgs flag (RequiredLogLevel a :: as) (x :: xs) f =
  do arg <- maybeToEither ("Expected LogLevel argument " ++ show x ++ " for flag " ++ flag)
                          (parseLogLevel x)
     processArgs flag as xs (f arg)
processArgs flag (AutoNat a :: as) ("auto" :: xs) f =
  processArgs flag as xs (f Nothing)
processArgs flag (AutoNat a :: as) (x :: xs) f =
  do arg <- maybeToEither ("Expected Nat or \"auto\" argument " ++ show x ++ " for flag " ++ flag)
                          (parseInteger x >>= checkNat)
     processArgs flag as xs (f (Just arg))
processArgs flag (Required a :: as) (x :: xs) f =
  processArgs flag as xs (f x)
processArgs flag (Optional a :: as) (x :: xs) f =
  processArgs flag as xs (f $ toMaybe (not (isPrefixOf "-" x)) x)

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

||| List of all command line option flags.
export
optionFlags : List String
optionFlags = options >>= flags
