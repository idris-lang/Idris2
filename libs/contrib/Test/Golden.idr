||| Core features required to perform Golden file testing.
|||
||| We provide the core functionality to run a *single* golden file test.
||| This allows the developer freedom to design the rest of the test harness.
|||
||| This was originally used as part of Idris2's own test suite and
||| the core functionality is useful for the many and not the few.
||| Please see Idris2 test harness for example usage.
|||
||| # Test Structure
|||
||| This harness works from the assumption that each individual golden test comprises of a directory with the following structure:
|||
||| + `run.sh` a *shell* script that runs the test
||| + `expected` the expected output of `run.sh`
|||
||| During testing, the test harness will generate an artefact named `output` and use `git diff` to examine the two files.
||| This assumes that the expected has been checked into `git`.
||| If `git diff` failes then the runner will simply present the expected and 'given' files.
|||
||| # Options
|||
||| The test harness has several options that must be set:
|||
||| + `idris2` the path of the executable we are testing.
||| + `onlyNames` the list of tests to run relative to the generated executable.
||| + `interactive` Should we update the expected file or not.
|||
||| # Usage
|||
||| When compiled to an executable the expected usage is:
|||
|||```sh
|||runtests <path to executable> [--interactive] [--only [NAMES]]
|||```
|||
||| assuming that the test runner is compiler to an executable named `runtests`.
module Test.Golden

import Data.Maybe
import Data.List
import Data.List1
import Data.Strings

import System
import System.Directory
import System.File
import System.Info
import System.Path

-- [ Options ]

||| Options for the test driver.
public export
record Options where
  constructor MkOptions
  ||| Name of the idris2 executable
  idris2      : String
  ||| Should we only run some specific cases?
  onlyNames   : List String
  ||| Should we run the test suite interactively?
  interactive : Bool

export
usage : String
usage = "Usage: runtests <path> [--interactive] [--only [NAMES]]"

||| Process the command line options.
export
options : List String -> Maybe Options
options args = case args of
    (_ :: idris2 :: rest) => go rest (MkOptions idris2 [] False)
    _ => Nothing

  where

    go : List String -> Options -> Maybe Options
    go rest opts = case rest of
      []                      => pure opts
      ("--interactive" :: xs) => go xs (record { interactive = True } opts)
      ("--only" :: xs)        => pure $ record { onlyNames = xs } opts
      _ => Nothing

-- [ Core ]

fail : String -> IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)


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

||| Run the specified Golden test with the supplied options.
|||
||| See the module documentation for more information.
|||
||| @currdir absolute or relative path to root test directory.
||| @testpath the directory that contains the test.
export
runTest : Options -> (currdir, testPath : String) -> IO Bool
runTest opts currdir testPath
    = do changeDir testPath
         isSuccess <- runTest'
         changeDir currdir
         pure isSuccess
    where
        getAnswer : IO Bool
        getAnswer = do
          str <- getLine
          case str of
            "y" => pure True
            "n" => pure False
            _   => do putStrLn "Invalid Answer."
                      getAnswer

        printExpectedVsOutput : String -> String -> IO ()
        printExpectedVsOutput exp out = do
          putStrLn "Expected:"
          printLn exp
          putStrLn "Given:"
          printLn out

        mayOverwrite : Maybe String -> String -> IO ()
        mayOverwrite mexp out = do
          the (IO ()) $ case mexp of
            Nothing => putStr $ unlines
              [ "Golden value missing. I computed the following result:"
              , out
              , "Accept new golden value? [yn]"
              ]
            Just exp => do
              putStrLn "Golden value differs from actual value."
              code <- system "git diff --no-index --exit-code --word-diff=color expected output"
              when (code < 0) $ printExpectedVsOutput exp out
              putStrLn "Accept actual value as new golden value? [yn]"
          b <- getAnswer
          when b $ do Right _ <- writeFile "expected" out
                          | Left err => print err
                      pure ()
        runTest' : IO Bool
        runTest'
            = do putStr $ testPath ++ ": "
                 system $ "sh ./run " ++ idris2 opts ++ " | tr -d '\\r' > output"
                 Right out <- readFile "output"
                     | Left err => do print err
                                      pure False
                 Right exp <- readFile "expected"
                     | Left FileNotFound => do
                         if interactive opts
                           then mayOverwrite Nothing out
                           else print FileNotFound
                         pure False
                     | Left err => do print err
                                      pure False
                 let result = normalize out == normalize exp
                 if result
                    then putStrLn "success"
                    else do
                      putStrLn "FAILURE"
                      if interactive opts
                         then mayOverwrite (Just exp) out
                         else printExpectedVsOutput exp out

                 pure result

||| Check if a file exists for reading.
export
exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

||| Find the first occurance of an executable on `PATH`.
export
pathLookup : List String -> IO (Maybe String)
pathLookup names = do
  path <- getEnv "PATH"
  let pathList = forget $ split (== pathSeparator) $ fromMaybe "/usr/bin:/usr/local/bin" path
  let candidates = [p ++ "/" ++ x | p <- pathList,
                                    x <- names]
  firstExists candidates
