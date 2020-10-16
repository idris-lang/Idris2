module Main

import Data.Maybe
import Data.List
import Data.List1
import Data.Strings

import System
import System.Directory
import System.File
import System.Info
import System.Path

%default covering

------------------------------------------------------------------------
-- Test cases

ttimpTests : List String
ttimpTests
    = ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006",
       "coverage001", "coverage002",
       "dot001",
       "eta001", "eta002",
       "lazy001",
       "nest001", "nest002",
       "perf001", "perf002", "perf003",
       "record001", "record002", "record003",
       "qtt001", "qtt003",
       "total001", "total002", "total003"]

idrisTests : List String
idrisTests
    = -- Fundamental language features
      ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006", "basic007", "basic008", "basic009", "basic010",
       "basic011", "basic012", "basic013", "basic014", "basic015",
       "basic016", "basic017", "basic018", "basic019", "basic020",
       "basic021", "basic022", "basic023", "basic024", "basic025",
       "basic026", "basic027", "basic028", "basic029", "basic030",
       "basic031", "basic032", "basic033", "basic034", "basic035",
       "basic036", "basic037", "basic038", "basic039", "basic040",
       "basic041", "basic042", "basic043", "basic044", "basic045",
       "basic046", "basic047",
       -- Coverage checking
       "coverage001", "coverage002", "coverage003", "coverage004",
       "coverage005", "coverage006", "coverage007", "coverage008",
       "coverage009", "coverage010",
       -- Documentation strings
       "docs001", "docs002",
       -- Evaluator
       "evaluator001", "evaluator002", "evaluator003",
       -- Error messages
       "error001", "error002", "error003", "error004", "error005",
       "error006", "error007", "error008", "error009", "error010",
       "error011", "error012", "error013",
       -- Modules and imports
       "import001", "import002", "import003", "import004", "import005",
       -- Interactive editing support
       "interactive001", "interactive002", "interactive003", "interactive004",
       "interactive005", "interactive006", "interactive007", "interactive008",
       "interactive009", "interactive010", "interactive011", "interactive012",
       "interactive013", "interactive014", "interactive015", "interactive016",
       "interactive017", "interactive018",
       -- Interfaces
       "interface001", "interface002", "interface003", "interface004",
       "interface005", "interface006", "interface007", "interface008",
       "interface009", "interface010", "interface011", "interface012",
       "interface013", "interface014", "interface015", "interface016",
       "interface017",
       -- Miscellaneous REPL
       "interpreter001", "interpreter002", "interpreter003", "interpreter004",
       "interpreter005",
       -- Implicit laziness, lazy evaluation
       "lazy001",
       -- QTT and linearity related
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "linear006", "linear007", "linear008", "linear009", "linear010",
       "linear011", "linear012",
       -- Literate
       "literate001", "literate002", "literate003", "literate004",
       "literate005", "literate006", "literate007", "literate008",
       "literate009", "literate010", "literate011", "literate012",
       "literate013", "literate014",
       -- Namespace blocks
       "namespace001",
       -- Parameters blocks
       "params001",
       -- Performance: things which have been slow in the past, or which
       -- pose interesting challenges for the elaborator
       "perf001", "perf002", "perf003", "perf004", "perf005",
       -- Parse errors
       "perror001", "perror002", "perror003", "perror004", "perror005",
       "perror006",
       -- Packages and ipkg files
       "pkg001", "pkg002", "pkg003", "pkg004", "pkg005",
       -- Positivity checking
       "positivity001", "positivity002", "positivity003",
       -- Larger programs arising from real usage. Typically things with
       -- interesting interactions between features
       "real001", "real002",
       -- Records, access and dependent update
       "record001", "record002", "record003", "record004", "record005",
       "record007",
       -- Quotation and reflection
       "reflection001", "reflection002", "reflection003", "reflection004",
       "reflection005", "reflection006", "reflection007", "reflection008",
       "reflection009",
       -- Miscellaneous regressions
       "reg001", "reg002", "reg003", "reg004", "reg005", "reg006", "reg007",
       "reg008", "reg009", "reg010", "reg011", "reg012", "reg013", "reg014",
       "reg015", "reg016", "reg017", "reg018", "reg019", "reg020", "reg021",
       "reg022", "reg023", "reg024", "reg025", "reg026", "reg027", "reg028",
       "reg029", "reg030", "reg031", "reg032", "reg033", "reg034",
       -- Totality checking
       "total001", "total002", "total003", "total004", "total005",
       "total006", "total007", "total008", "total009", "total010",
       -- The 'with' rule
       "with001", "with002",
       -- with-disambiguation
       "with003"]

typeddTests : List String
typeddTests
   = ["chapter01", "chapter02", "chapter03", "chapter04", "chapter05",
      "chapter06", "chapter07", "chapter08", "chapter09", "chapter10",
      "chapter11", "chapter12", "chapter13", "chapter14"]

chezTests : List String
chezTests
   = ["chez001", "chez002", "chez003", "chez004", "chez005", "chez006",
      "chez007", "chez008", "chez009", "chez010", "chez011", "chez012",
      "chez013", "chez014", "chez015", "chez016", "chez017", "chez018",
      "chez019", "chez020", "chez021", "chez022", "chez023", "chez024",
      "chez025", "chez026", "chez027", "chez028", "chez029", "chez030",
      "chez031",
      "perf001",
      "reg001"]

nodeTests : List String
nodeTests
  = [ "node001", "node002", "node003", "node004", "node005", "node006", "node007", "node008", "node009"
    , "node011", "node012", "node015", "node017", "node018", "node019" -- node014
    , "node021", "node022" --, "node020"
    , "reg001"
    , "syntax001"
    , "tailrec001"
    , "idiom001"
    ]

ideModeTests : List String
ideModeTests
  =  [ "ideMode001", "ideMode002", "ideMode003", "ideMode004" ]

preludeTests : List String
preludeTests
  =  [ "reg001" ]

------------------------------------------------------------------------
-- Options

||| Options for the test driver.
record Options where
  constructor MkOptions
  ||| Name of the idris2 executable
  idris2      : String
  ||| Name of the codegenerator to use for `exec`
  codegen     : Maybe String
  ||| Should we only run some specific cases?
  onlyNames   : List String
  ||| Should we run the test suite interactively?
  interactive : Bool

usage : String
usage = "Usage: runtests <idris2 path> [--interactive] [--only [NAMES]]"

options : List String -> Maybe Options
options args = case args of
    (_ :: idris2 :: rest) => go rest (MkOptions idris2 Nothing [] False)
    _ => Nothing

  where

    go : List String -> Options -> Maybe Options
    go rest opts = case rest of
      []                      => pure opts
      ("--interactive" :: xs) => go xs (record { interactive = True } opts)
      ("--cg" :: cg :: xs)    => go xs (record { codegen = Just cg } opts)
      ("--only" :: xs)        => pure $ record { onlyNames = xs } opts
      _ => Nothing

------------------------------------------------------------------------
-- Actual test runner

fail : String -> IO ()
fail err
    = do putStrLn err
         exitWith (ExitFailure 1)

-- on Windows, we just ignore backslashes and slashes when comparing,
-- similarity up to that is good enough. Leave errors that depend
-- on the confusion of slashes and backslashes to unix machines.
normalize : String -> String
normalize str =
    if isWindows
      then pack $ filter (\ch => ch /= '/' && ch /= '\\') (unpack str)
      else str

runTest : Options -> String -> IO Bool
runTest opts testPath
    = do changeDir testPath
         isSuccess <- runTest'
         changeDir "../.."
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
                 let cg = case codegen opts of
                            Nothing => ""
                            Just cg => "env IDRIS2_TESTS_CG=" ++ cg ++ " "
                 system $ cg ++ "sh ./run " ++ idris2 opts ++ " | tr -d '\\r' > output"
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

exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

pathLookup : List String -> IO (Maybe String)
pathLookup names = do
  path <- getEnv "PATH"
  let pathList = forget $ split (== pathSeparator) $ fromMaybe "/usr/bin:/usr/local/bin" path
  let candidates = [p ++ "/" ++ x | p <- pathList,
                                    x <- names]
  firstExists candidates

findChez : IO (Maybe String)
findChez
    = do Just chez <- getEnv "CHEZ" | Nothing => pathLookup ["chez", "chezscheme9.5", "scheme", "scheme.exe"]
         pure $ Just chez

findNode : IO (Maybe String)
findNode
    = do Just chez <- getEnv "NODE" | Nothing => pathLookup ["node"]
         pure $ Just chez

findRacket : IO (Maybe String)
findRacket
  = do Just racket <- getEnv "RACKET" | Nothing => pathLookup ["racket"]
       pure $ Just racket

findCG : IO (Maybe String)
findCG
  = do Nothing <- getEnv "IDRIS2_CG" | p => pure p
       Nothing <- findChez   | p => pure (Just "chez")
       Nothing <- findNode   | p => pure (Just "node")
       Nothing <- findRacket | p => pure (Just "racket")
       pure Nothing

runChezTests : Options -> List String -> IO (List Bool)
runChezTests opts tests
    = do chexec <- findChez
         maybe (do putStrLn "Chez Scheme not found"
                   pure [])
               (\c => do putStrLn $ "Found Chez Scheme at " ++ c
                         traverse (runTest opts) tests)
               chexec

runNodeTests : Options -> List String -> IO (List Bool)
runNodeTests opts tests
    = do nodeexec <- findNode
         maybe (do putStrLn "node not found"
                   pure [])
               (\c => do putStrLn $ "Found node at " ++ c
                         traverse (runTest opts) tests)
               nodeexec


filterTests : Options -> List String -> List String
filterTests opts = case onlyNames opts of
  [] => id
  xs => filter (\ name => any (`isInfixOf` name) xs)

main : IO ()
main
    = do args <- getArgs
         let (Just opts) = options args
              | _ => do print args
                        putStrLn usage
         opts <- case codegen opts of
                   Nothing => pure $ record { codegen = !findCG } opts
                   Just _ => pure opts
         let filteredNonCGTests =
              filterTests opts $ concat $
                 [ testPaths "ttimp" ttimpTests
                 , testPaths "idris2" idrisTests
                 , testPaths "typedd-book" typeddTests
                 , testPaths "ideMode" ideModeTests
                 , testPaths "prelude" preludeTests
                 ]
         let filteredChezTests = filterTests opts (testPaths "chez" chezTests)
         let filteredNodeTests = filterTests opts (testPaths "node" nodeTests)
         nonCGTestRes <- traverse (runTest opts) filteredNonCGTests
         chezTestRes <- if length filteredChezTests > 0
              then runChezTests opts filteredChezTests
              else pure []
         nodeTestRes <- if length filteredNodeTests > 0
              then runNodeTests opts filteredNodeTests
              else pure []
         let res = nonCGTestRes ++ chezTestRes ++ nodeTestRes
         putStrLn (show (length (filter id res)) ++ "/" ++ show (length res)
                       ++ " tests successful")
         if (any not res)
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess
    where
         testPaths : String -> List String -> List String
         testPaths dir tests = map (\test => dir ++ "/" ++ test) tests
