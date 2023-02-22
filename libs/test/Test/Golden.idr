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
|||  git diff --no-index --exit-code --word-diff-regex=. --color expected output
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
|||   [[--only|--except] [NAMES]]
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
import Data.String.Extra

import System
import System.Clock
import System.Directory
import System.File
import System.Info
import System.Path
import System.Concurrency

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
  onlyNames    : Maybe (String -> Bool)
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
              Nothing
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
  , "[[--only|--except] [NAMES]]"
  ]

optionsTestsFilter : List String -> List String -> Maybe (String -> Bool)
optionsTestsFilter [] [] = Nothing
optionsTestsFilter only except = Just $ \ name =>
  let onlyCheck = null only || any (`isInfixOf` name) only in
  let exceptCheck = all (not . (`isInfixOf` name)) except in
  onlyCheck && exceptCheck

record Acc where
  constructor MkAcc
  onlyFile : Maybe String
  onlyNames : List String
  exceptNames : List String
initAcc : Acc
initAcc = MkAcc Nothing [] []

||| Process the command line options.
export
options : List String -> IO (Maybe Options)
options args = case args of
    (_ :: exe :: rest) => mkOptions exe rest
    _ => pure Nothing

  where

    isFlag : String -> Bool
    isFlag str = "--" `isPrefixOf` str

    go : List String -> Acc -> Options -> Maybe (Acc, Options)
    go rest acc opts = case rest of
      []                            => pure (acc, opts)
      ("--timing" :: xs)            => go xs acc ({ timing := True} opts)
      ("--interactive" :: xs)       => go xs acc ({ interactive := True } opts)
      ("--color"  :: xs)            => go xs acc ({ color := True } opts)
      ("--colour" :: xs)            => go xs acc ({ color := True } opts)
      ("--no-color"  :: xs)         => go xs acc ({ color := False } opts)
      ("--no-colour" :: xs)         => go xs acc ({ color := False } opts)
      ("--cg" :: cg :: xs)          => go xs acc ({ codegen := Just cg } opts)
      ("--threads" :: n :: xs)      => do let pos : Nat = !(parsePositive n)
                                          go xs acc ({ threads := pos } opts)
      ("--failure-file" :: p :: xs) => go  xs acc ({ failureFile := Just p } opts)
      ("--only" :: p :: xs)         =>
        ifThenElse (isFlag p)
          (go (p :: xs) acc opts)
          (go xs ({ onlyNames $= (words p ++) } acc) opts)
      ("--except" :: p :: xs)       =>
        ifThenElse (isFlag p)
          (go (p :: xs) acc opts)
          (go xs ({ exceptNames $= (words p ++) } acc) opts)
      ("--only-file" :: p :: xs)    => go xs ({ onlyFile := Just p } acc) opts
      [p] => do guard (p `elem` ["--only", "--except"])
                pure (acc, opts)
                -- ^ we accept trailing only or except flags as unused (do not filter out any tests)
                -- for the convenience of populating these options from shell scripts.
      _ => Nothing

    mkOptions : String -> List String -> IO (Maybe Options)
    mkOptions exe rest
      = do color <- [ (isNothing noc) && tty | noc <- getEnv "NO_COLOR", tty <- isTTY stdout ]
           let Just (acc, opts) = go rest initAcc (initOptions exe color)
                 | Nothing => pure Nothing
           extraOnlyNames <- the (IO (List String)) $ case acc.onlyFile of
                               Nothing => pure []
                               Just fp => do Right only <- readFile fp
                                               | Left err => die (show err)
                                             pure (lines only)
           pure $ Just $ { onlyNames := optionsTestsFilter (extraOnlyNames ++ acc.onlyNames) acc.exceptNames } opts

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
runTest : Options -> (testPath : String) -> IO Result
runTest opts testPath = do
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

    badSystemExitCode : Int -> Bool
    badSystemExitCode code = code < 0 || code == 127 {- 127 means shell couldn't start -}

    mayOverwrite : Maybe String -> String -> IO ()
    mayOverwrite mexp out = do
      case mexp of
        Nothing => putStr $ unlines
          [ "Golden value missing. I computed the following result:"
          , maybeColored BrightBlue out
          , "Accept new golden value? [y/N]"
          ]
        Just exp => do
          code <- system $ "git diff --no-index --exit-code --word-diff-regex=. " ++
            (if opts.color then  "--color " else "") ++
            escapeArg testPath ++ "/expected " ++ escapeArg testPath ++ "/output"
          putStr . unlines $
            ["Golden value differs from actual value."] ++
            (if badSystemExitCode code then expVsOut exp out else []) ++
            ["Accept actual value as new golden value? [y/N]"]
      b <- getAnswer
      when b $ do Right _ <- writeFile (testPath ++ "/expected") out
                    | Left err => putStrLn $ (testPath ++ "/expected") ++ ": " ++ show err
                  pure ()

    printTiming : Bool -> Clock type -> String -> String -> IO ()
    printTiming False _     path msg = putStrLn $ concat [path, ": ", msg]
    printTiming True  clock path msg =
      let time  = showTime 2 3 clock
          width = 72
          -- We use 9 instead of `String.length msg` because:
          -- 1. ": success" and ": FAILURE" have the same length
          -- 2. ANSI escape codes make the msg look longer than it is
          msgl  = 9
          path  = leftEllipsis (width `minus` (1 + msgl + length time)) "(...)" path
          spent = length time + length path + msgl
          pad   = pack $ replicate (width `minus` spent) ' '
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
Eq Requirement where
  C == C = True
  Chez == Chez = True
  Node == Node = True
  Racket == Racket = True
  Gambit == Gambit = True
  _ == _ = False

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
    | Left e => die $ "failed to list " ++ dirName ++ ": " ++ show e
  let names = [n | n <- names, testNameFilter n]
  let testNames = [dirName ++ "/" ++ n | n <- names]
  testNames <- filter testNames
  when (length testNames == 0) $ die $ "no tests found in " ++ dirName
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
  Nothing => id
  Just f  => filter f

||| The summary of a test pool run
public export
record Summary where
  constructor MkSummary
  success : List String
  failure : List String

||| A new, blank summary
export
initSummary : Summary
initSummary = MkSummary [] []

||| Update the summary to contain the given result
export
updateSummary : (newRes : Result) -> Summary -> Summary
updateSummary newRes =
  case newRes of
       Left l  => { failure $= (l ::) }
       Right w => { success $= (w ::) }

||| Update the summary to contain the given results
export
bulkUpdateSummary : (newRess : List Result) -> Summary -> Summary
bulkUpdateSummary newRess =
  let (ls, ws) = partitionEithers newRess in
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

||| An instruction to a thread which runs tests
public export
data ThreadInstruction : Type where
  ||| A test to run
  Run : (test : String) -> ThreadInstruction
  ||| An indication for the thread to stop
  Stop : ThreadInstruction

||| Sends the given tests on the given @Channel@, then sends `nThreads` many
||| 'Stop' @ThreadInstruction@s to stop the threads running the tests.
|||
||| @testChan The channel to send the tests over.
||| @nThreads The number of threads being used to run the tests.
||| @tests The list of tests to send to the runners/threads.
export
testSender : (testChan : Channel ThreadInstruction) -> (nThreads : Nat)
           -> (tests : List String) -> IO ()
testSender testChan 0 [] = pure ()
testSender testChan (S k) [] =
  -- out of tests, so the next thing for all the threads is to stop
  do channelPut testChan Stop
     testSender testChan k []
testSender testChan nThreads (test :: tests) =
  do channelPut testChan (Run test)
     testSender testChan nThreads tests

||| A result from a test-runner/thread
public export
data ThreadResult : Type where
  ||| The result of running a test
  Res : (res : Result) -> ThreadResult
  ||| An indication that the thread was told to stop
  Done : ThreadResult

||| Receives results on the given @Channel@, accumulating them as a @Summary@.
||| When all results have been received (i.e. @nThreads@ many 'Done'
||| @ThreadInstruction@s have been encountered), send the resulting Summary over
||| the @accChan@ Channel (necessary to be able to @fork@ this function and
||| still obtain the Summary at the end).
|||
||| @resChan The channel to receives the results on.
||| @acc The Summary acting as an accumulator.
||| @accChan The Channel to send the final Summary over.
||| @nThreads The number of threads being used to run the tests.
export
testReceiver : (resChan : Channel ThreadResult) -> (acc : Summary)
             -> (accChan : Channel Summary) -> (nThreads : Nat) -> IO ()
testReceiver resChan acc accChan 0 = channelPut accChan acc
testReceiver resChan acc accChan nThreads@(S k) =
  do (Res res) <- channelGet resChan
        | Done => testReceiver resChan acc accChan k
     testReceiver resChan (updateSummary res acc) accChan nThreads

||| Function responsible for receiving and running tests.
|||
||| @opts The options to run the threads under.
||| @testChan The Channel to receive tests on.
||| @resChan The Channel to send results over.
testThread : (opts : Options) -> (testChan : Channel ThreadInstruction)
              -> (resChan : Channel ThreadResult) -> IO ()
testThread opts testChan resChan =
  do (Run test) <- channelGet testChan
        | Stop => channelPut resChan Done
     res <- runTest opts test
     channelPut resChan (Res res)
     testThread opts testChan resChan

||| A runner for a test pool. If there are tests in the @TestPool@ that we want
||| to run, spawns `opts.threads` many runners and sends them the tests,
||| collecting all the results in the @Summary@ returned at the end.
|||
||| @opts The options for the TestPool.
||| @pool The TestPool to run.
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

       -- set up the channels
       accChan <- makeChannel
       resChan <- makeChannel
       testChan <- makeChannel

       -- and then run all the tests

       for_ (replicate opts.threads 0) $ \_ =>
         fork (testThread opts testChan resChan)
       -- start sending tests
       senderTID <- fork $ testSender testChan opts.threads tests
       -- start receiving results
       receiverTID <- fork $ testReceiver resChan initSummary accChan opts.threads
       -- wait until things are done, i.e. until we receive the final acc
       acc <- channelGet accChan
       pure acc

  where

    separator : String
    separator = fastPack $ replicate 72 '-'

    banner : List String -> String
    banner msgs = fastUnlines
        $ [ "", separator, pool.poolName ]
       ++ msgs
       ++ [ separator ]

export
runnerWith : Options -> List TestPool -> IO ()
runnerWith opts tests = do

         -- if no CG has been set, find a sensible default based on what is available
         opts <- case codegen opts of
                   Nothing => pure $ { codegen := !findCG } opts
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
                | Left err => die (show err)
              pure ()

         -- exit
         if nfail == 0
           then exitSuccess
           else exitFailure

||| A runner for a whole test suite
export
runner : List TestPool -> IO ()
runner tests
    = do args <- getArgs
         Just opts <- options args
            | _ => do printLn args
                      putStrLn usage
         runnerWith opts tests
