||| Core features required to perform Golden file testing.
|||
||| We provide the core functionality to run a *single* golden file test, or
||| a whole test tree.
||| This allows the developer freedom to use as is or design the rest of the
||| test harness to their liking.
|||
||| This was originally used as part of Idris2's own test suite and
||| the core functionality is useful for the many and not the few.
||| Please see Idris2 test harness for example usage.
|||
||| # Test Structure
|||
||| This harness works from the assumption that each individual golden test
||| comprises of a directory with the following structure:
|||
||| + `run` a *shell* script that runs the test. We expect it to:
|||   * Use `$1` as the variable standing for the idris executable to be tested
|||   * May use `${IDRIS2_TESTS_CG}` to pick a codegen that ought to work
|||   * Clean up after itself (e.g. by running `rm -rf build/`)
|||
||| + `expected` a file containting the expected output of `run`
|||
||| During testing, the test harness will generate an artefact named `output`
||| and display both outputs if there is a failure.
||| During an interactive session the following command is used to compare them
||| as they are:
|||
||| ```sh
|||  git diff --no-index --exit-code --word-diff=color expected output
||| ```
|||
||| If `git` fails then the runner will simply present the expected and 'given'
||| files side-by-side.
|||
||| Of note, it is helpful to add `output` to a local `.gitignore` instance
||| to ensure that it is not mistakenly versioned.
|||
||| # Options
|||
||| The test harness has several options that may be set:
|||
||| + `idris2`       The path of the executable we are testing.
||| + `codegen`      The backend to use for code generation.
||| + `onlyNames`    The tests to run relative to the generated executable.
||| + `onlyFile`     The file listing the tests to run relative to the generated executable.
||| + `interactive`  Whether to offer to update the expected file or not.
||| + `timing`       Whether to display time taken for each test.
||| + `threads`      The maximum numbers to use (default: number of cores).
||| + `failureFile`  The file in which to write the list of failing tests.
|||
||| We provide an options parser (`options`) that takes the list of command line
||| arguments and constructs this for you.
|||
||| # Usage
|||
||| When compiled to an executable the expected usage is:
|||
|||```sh
||| runtests <path to executable under test>
|||   [--timing]
|||   [--interactive]
|||   [--only-file PATH]
|||   [--failure-file PATH]
|||   [--threads N]
|||   [--cg CODEGEN]
|||   [--only [NAMES]]
|||```
|||
||| assuming that the test runner is compiled to an executable named `runtests`.

module Test.Golden

import Control.ANSI

import Data.Either
import Data.Maybe
import Data.List
import Data.List1
import Data.String

import System
import System.Clock
import System.Directory
import System.File
import System.Future
import System.Info
import System.Path

-- [ Options ]

||| Options for the test driver.
public export
record Options where
  constructor MkOptions
  ||| Name of the idris2 executable
  exeUnderTest : String
  ||| Which codegen should we use?
  codegen      : Maybe String
  ||| Should we only run some specific cases?
  onlyNames    : List String
  ||| Should we run the test suite interactively?
  interactive  : Bool
  ||| Should we use colors?
  color        : Bool
  ||| Should we time and display the tests
  timing       : Bool
  ||| How many threads should we use?
  threads      : Nat
  ||| Should we write the list of failing cases to a file?
  failureFile     : Maybe String

export
initOptions : String -> Bool -> Options
initOptions exe color
  = MkOptions exe
              Nothing
              []
              False
              color
              False
              1
              Nothing

export
usage : String
usage = unwords
  ["Usage:"
  , "runtests <path>"
  , "[--timing]"
  , "[--interactive]"
  , "[--[no-]color, --[no-]colour]"
  , "[--cg CODEGEN]"
  , "[--threads N]"
  , "[--failure-file PATH]"
  , "[--only-file PATH]"
  , "[--only [NAMES]]"
  ]

export
fail : String -> IO a
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

||| Process the command line options.
export
options : List String -> IO (Maybe Options)
options args = case args of
    (_ :: exe :: rest) => mkOptions exe rest
    _ => pure Nothing

  where

    go : List String -> Maybe String -> Options -> Maybe (Maybe String, Options)
    go rest only opts = case rest of
      []                            => pure (only, opts)
      ("--timing" :: xs)            => go xs only (record { timing = True} opts)
      ("--interactive" :: xs)       => go xs only (record { interactive = True } opts)
      ("--color"  :: xs)            => go xs only (record { color = True } opts)
      ("--colour" :: xs)            => go xs only (record { color = True } opts)
      ("--no-color"  :: xs)         => go xs only (record { color = False } opts)
      ("--no-colour" :: xs)         => go xs only (record { color = False } opts)
      ("--cg" :: cg :: xs)          => go xs only (record { codegen = Just cg } opts)
      ("--threads" :: n :: xs)      => do let pos : Nat = !(parsePositive n)
                                          go xs only (record { threads = pos } opts)
      ("--failure-file" :: p :: xs) => go  xs only (record { failureFile = Just p } opts)
      ("--only" :: xs)              => pure (only, record { onlyNames = xs } opts)
      ("--only-file" :: p :: xs)    => go xs (Just p) opts
      _ => Nothing

    mkOptions : String -> List String -> IO (Maybe Options)
    mkOptions exe rest
      = do color <- (Just "DUMB" /=) <$> getEnv "TERM"
           let Just (mfp, opts) = go rest Nothing (initOptions exe color)
                 | Nothing => pure Nothing
           let Just fp = mfp
                 | Nothing => pure (Just opts)
           Right only <- readFile fp
             | Left err => fail (show err)
           pure $ Just $ record { onlyNames $= ((lines only) ++) } opts

||| Normalise strings between different OS.
|||
||| on Windows, we just ignore backslashes and slashes when comparing,
||| similarity up to that is good enough. Leave errors that depend
||| on the confusion of slashes and backslashes to unix machines.
normalize : String -> String
normalize str =
    if isWindows
      then pack $ filter (\ch => ch /= '/' && ch /= '\\') (unpack str)
      else str

||| The result of a test run
||| `Left` corresponds to a failure, and `Right` to a success
Result : Type
Result = Either String String

||| Run the specified Golden test with the supplied options.
||| See the module documentation for more information.
||| @testPath the directory that contains the test.
export
runTest : Options -> (testPath : String) -> IO (Future Result)
runTest opts testPath = forkIO $ do
  start <- clockTime UTC
  let cg = maybe "" (" --cg " ++) (codegen opts)
  let exe = "\"" ++ exeUnderTest opts ++ cg ++ "\""
  ignore $ system $ "cd " ++ escapeArg testPath ++ " && " ++
    "sh ./run " ++ exe ++ " | tr -d '\\r' > output"
  end <- clockTime UTC

  Right out <- readFile $ testPath ++ "/output"
    | Left err => do putStrLn $ (testPath ++ "/output") ++ ": " ++ show err
                     pure (Left testPath)

  Right exp <- readFile $ testPath ++ "/expected"
    | Left FileNotFound => do
        if interactive opts
          then mayOverwrite Nothing out
          else putStrLn $ (testPath ++ "/expected") ++ ": " ++ show FileNotFound
        pure (Left testPath)
    | Left err => do putStrLn $ (testPath ++ "/expected") ++ ": " ++ show err
                     pure (Left testPath)

  let result = normalize out == normalize exp
  let time = timeDifference end start

  if result
    then printTiming opts.timing time testPath $ maybeColored BrightGreen "success"
    else do
      printTiming opts.timing time testPath $ maybeColored BrightRed "FAILURE"
      if interactive opts
        then mayOverwrite (Just exp) out
        else putStr . unlines $ expVsOut exp out

  pure $ if result then Right testPath else Left testPath

  where
    getAnswer : IO Bool
    getAnswer = do
      str <- getLine
      case str of
        "y" => pure True
        "n" => pure False
        "N" => pure False
        ""  => pure False
        _   => do putStrLn "Invalid answer."
                  getAnswer

    maybeColored : Color -> String -> String
    maybeColored c = if opts.color then show . colored c else id

    expVsOut : String -> String -> List String
    expVsOut exp out = ["Expected:", maybeColored Green exp, "Given:", maybeColored Red out]

    mayOverwrite : Maybe String -> String -> IO ()
    mayOverwrite mexp out = do
      case mexp of
        Nothing => putStr $ unlines
          [ "Golden value missing. I computed the following result:"
          , maybeColored BrightBlue out
          , "Accept new golden value? [y/N]"
          ]
        Just exp => do
          code <- system $ "git diff --no-index --exit-code " ++
            (if opts.color then  "--word-diff=color " else "") ++
            escapeArg testPath ++ "/expected " ++ escapeArg testPath ++ "/output"
          putStr . unlines $
            ["Golden value differs from actual value."] ++
            (if (code < 0) then expVsOut exp out else []) ++
            ["Accept actual value as new golden value? [y/N]"]
      b <- getAnswer
      when b $ do Right _ <- writeFile (testPath ++ "/expected") out
                    | Left err => putStrLn $ (testPath ++ "/expected") ++ ": " ++ show err
                  pure ()

    printTiming : Bool -> Clock type -> String -> String -> IO ()
    printTiming False _     path msg = putStrLn $ concat [path, ": ", msg]
    printTiming True  clock path msg =
      let time  = showTime 2 3 clock
          -- We use 9 instead of `String.length msg` because:
          -- 1. ": success" and ": FAILURE" have the same length
          -- 2. ANSI escape codes make the msg look longer than it is
          spent = String.length time + String.length path + 9
          pad   = pack $ replicate (minus 72 spent) ' '
      in putStrLn $ concat [path, ": ", msg, pad, time]

||| Find the first occurrence of an executable on `PATH`.
export
pathLookup : List String -> IO (Maybe String)
pathLookup names = do
  path <- getEnv "PATH"
  let extensions = if isWindows then [".exe", ".cmd", ".bat", ""] else [""]
  let pathList = forget $ split (== pathSeparator) $ fromMaybe "/usr/bin:/usr/local/bin" path
  let candidates = [p ++ "/" ++ x ++ y | p <- pathList,
                                         x <- names,
                                         y <- extensions]
  firstExists candidates


||| Some test may involve Idris' backends and have requirements.
||| We define here the ones supported by Idris
public export
data Requirement = C | Chez | Node | Racket | Gambit

export
Show Requirement where
  show C = "C"
  show Chez = "Chez"
  show Node = "node"
  show Racket = "racket"
  show Gambit = "gambit"

export
[CG] Show Requirement where
  show C = "refc"
  show Chez = "chez"
  show Node = "node"
  show Racket = "racket"
  show Gambit = "gambit"

export
checkRequirement : Requirement -> IO (Maybe String)
checkRequirement req
  = if platformSupport req
      then do let (envvar, paths) = requirement req
              Just exec <- getEnv envvar | Nothing => pathLookup paths
              pure (Just exec)
      else pure Nothing
  where
    requirement : Requirement -> (String, List String)
    requirement C = ("CC", ["cc"])
    requirement Chez = ("CHEZ", ["chez", "chezscheme9.5", "chezscheme", "chez-scheme", "scheme"])
    requirement Node = ("NODE", ["node"])
    requirement Racket = ("RACKET", ["racket"])
    requirement Gambit = ("GAMBIT", ["gsc"])
    platformSupport : Requirement -> Bool
    platformSupport C = not isWindows
    platformSupport Racket = not isWindows
    platformSupport _ = True

export
findCG : IO (Maybe String)
findCG
  = do Nothing <- getEnv "IDRIS2_TESTS_CG" | p => pure p
       Nothing <- checkRequirement Chez    | p => pure (Just "chez")
       Nothing <- checkRequirement Node    | p => pure (Just "node")
       Nothing <- checkRequirement Racket  | p => pure (Just "racket")
       Nothing <- checkRequirement Gambit  | p => pure (Just "gsc")
       Nothing <- checkRequirement C       | p => pure (Just "refc")
       pure Nothing

||| A choice of a codegen
public export
data Codegen
  = ||| Do NOT pass a cg argument to the executable being tested
    Nothing
  | ||| Use whatever the test runner was passed at the toplevel,
    ||| and if nothing was passed guess a sensible default using findCG
    Default
  | ||| Use exactly the given requirement
    Just Requirement

export
toList : Codegen -> List Requirement
toList (Just r) = [r]
toList _ = []

||| A test pool is characterised by
|||  + a name
|||  + a list of requirement
|||  + a choice of codegen (overriding the default)
|||  + and a list of directory paths
public export
record TestPool where
  constructor MkTestPool
  poolName : String
  constraints : List Requirement
  codegen : Codegen
  testCases : List String

||| Find all the test in the given directory.
export
testsInDir : (dirName : String) -> (testNameFilter : String -> Bool) -> (poolName : String) -> List Requirement -> Codegen -> IO TestPool
testsInDir dirName testNameFilter poolName reqs cg = do
  Right names <- listDir dirName
    | Left e => do putStrLn ("failed to list " ++ dirName ++ ": " ++ show e)
                   exitFailure
  let names = [n | n <- names, testNameFilter n]
  let testNames = [dirName ++ "/" ++ n | n <- names]
  testNames <- filter testNames
  when (length testNames == 0) $ do
    putStrLn ("no tests found in " ++ dirName)
    exitFailure
  pure $ MkTestPool poolName reqs cg testNames
    where
      -- Directory without `run` file is not a test
      isTest : (path : String) -> IO Bool
      isTest path = exists (path ++ "/run")

      filter : (testPaths : List String) -> IO (List String)
      filter [] = pure []
      filter (p :: ps) =
          do rem <- filter ps
             case !(isTest p) of
               True  => pure $ p :: rem
               False => pure rem


||| Only keep the tests that have been asked for
export
filterTests : Options -> List String -> List String
filterTests opts = case onlyNames opts of
  [] => id
  xs => filter (\ name => any (`isInfixOf` name) xs)

||| The summary of a test pool run
public export
record Summary where
  constructor MkSummary
  success : List String
  failure : List String

export
initSummary : Summary
initSummary = MkSummary [] []

export
updateSummary : List Result -> Summary -> Summary
updateSummary res =
  let (ls, ws) = partitionEithers res in
  { success $= (ws ++)
  , failure $= (ls ++)
  }

export
Semigroup Summary where
  MkSummary ws1 ls1 <+> MkSummary ws2 ls2
    = MkSummary (ws1 ++ ws2) (ls1 ++ ls2)

export
Monoid Summary where
  neutral = initSummary

||| A runner for a test pool
export
poolRunner : Options -> TestPool -> IO Summary
poolRunner opts pool
  = do -- check that we indeed want to run some of these tests
       let tests = filterTests opts (testCases pool)
       let (_ :: _) = tests
             | [] => pure initSummary
       -- if so make sure the constraints are satisfied
       cs <- for (toList (codegen pool) ++ constraints pool) $ \ req => do
          mfp <- checkRequirement req
          let msg = case mfp of
                      Nothing => "✗ " ++ show req ++ " not found"
                      Just fp => "✓ Found " ++ show req ++ " at " ++ fp
          pure (mfp, msg)
       let (cs, msgs) = unzip cs

       putStrLn (banner msgs)

       let Just _ = the (Maybe (List String)) (sequence cs)
             | Nothing => pure initSummary

       -- if the test pool requires a specific codegen then use that
       let opts = case codegen pool of
                    Nothing => { codegen := Nothing } opts
                    Just cg => { codegen := Just (show @{CG} cg) } opts
                    Default => opts
       -- if so run them all!
       loop opts initSummary tests

  where

    separator : String
    separator = fastPack $ replicate 72 '-'

    banner : List String -> String
    banner msgs = fastUnlines
        $ [ "", separator, pool.poolName ]
       ++ msgs
       ++ [ separator ]

    loop : Options -> Summary -> List String -> IO Summary
    loop opts acc [] = pure acc
    loop opts acc tests
      = do let (now, later) = splitAt opts.threads tests
           bs <- map await <$> traverse (runTest opts) now
           loop opts (updateSummary bs acc) later


||| A runner for a whole test suite
export
runner : List TestPool -> IO ()
runner tests
    = do args <- getArgs
         Just opts <- options args
            | _ => do printLn args
                      putStrLn usage
         -- if no CG has been set, find a sensible default based on what is available
         opts <- case codegen opts of
                   Nothing => pure $ record { codegen = !findCG } opts
                   Just _ => pure opts
         -- run the tests
         res <- concat <$> traverse (poolRunner opts) tests

         -- report the result
         let nsucc  = length res.success
         let nfail  = length res.failure
         let ntotal = nsucc + nfail
         putStrLn (show nsucc ++ "/" ++ show ntotal ++ " tests successful")

         -- deal with failures
         let list = fastUnlines res.failure
         when (nfail > 0) $
           do putStrLn "Failing tests:"
              putStr list
         -- always overwrite the failure file, if it is given
         whenJust opts.failureFile $ \ path =>
           do Right _ <- writeFile path list
                | Left err => fail (show err)
              pure ()

         -- exit
         if nfail == 0
           then exitWith ExitSuccess
           else exitWith (ExitFailure 1)
