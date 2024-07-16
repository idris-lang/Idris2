module Main

import System
import System.Directory
import System.File

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

ttimpTests : IO TestPool
ttimpTests = testsInDir "ttimp" "TTImp"

idrisTestsBasic : IO TestPool
idrisTestsBasic = testsInDir "idris2/basic" "Fundamental language features"

idrisTestsDebug : IO TestPool
idrisTestsDebug = testsInDir "idris2/debug" "Debug features"

idrisTestsCoverage : IO TestPool
idrisTestsCoverage = testsInDir "idris2/coverage" "Coverage checking"

idrisTestsTermination : IO TestPool
idrisTestsTermination = testsInDir "idris2/termination" "Termination checking"

idrisTestsCasetree : IO TestPool
idrisTestsCasetree = testsInDir "idris2/casetree" "Case tree building"

idrisTestsWarning : IO TestPool
idrisTestsWarning = testsInDir "idris2/warning" "Warnings"

idrisTestsFailing : IO TestPool
idrisTestsFailing = testsInDir "idris2/failing" "Failing blocks"

||| Error messages, including parse errors ("perror")
idrisTestsError : IO TestPool
idrisTestsError = testsInDir "idris2/error" "Error messages"

idrisTestsInteractive : IO TestPool
idrisTestsInteractive = testsInDir "idris2/interactive" "Interactive editing"

idrisTestsInterface : IO TestPool
idrisTestsInterface = testsInDir "idris2/interface" "Interface"

||| QTT and linearity related
idrisTestsLinear : IO TestPool
idrisTestsLinear = testsInDir "idris2/linear" "Quantities"

idrisTestsLiterate : IO TestPool
idrisTestsLiterate = testsInDir "idris2/literate" "Literate programming"

||| Performance: things which have been slow in the past, or which
||| pose interesting challenges for the elaborator
idrisTestsPerformance : IO TestPool
idrisTestsPerformance = testsInDir "idris2/perf" "Performance"

idrisTestsRegression : IO TestPool
idrisTestsRegression = testsInDir "idris2/reg" "Various regressions"

||| Data types, including records
idrisTestsData : IO TestPool
idrisTestsData = testsInDir "idris2/data" "Data and record types"

||| %builtin related tests for the frontend (type-checking)
idrisTestsBuiltin : IO TestPool
idrisTestsBuiltin = testsInDir "idris2/builtin" "Builtin types and functions"

||| Evaluator, REPL, specialisation
idrisTestsEvaluator : IO TestPool
idrisTestsEvaluator = testsInDir "idris2/evaluator" "Evaluation"

idrisTestsREPL : IO TestPool
idrisTestsREPL = testsInDir "idris2/repl" "REPL commands and help"

idrisTestsAllSchemes : Requirement -> IO TestPool
idrisTestsAllSchemes cg = testsInDir "allschemes"
      ("Test across all scheme backends: " ++ show cg ++ " instance")
      {codegen = Just cg}

idrisTestsAllBackends : Requirement -> TestPool
idrisTestsAllBackends cg = MkTestPool
      ("Test across all backends: " ++ show cg ++ " instance")
      [] (Just cg)
       -- RefC implements IEEE standard and distinguishes between 0.0 and -0.0
       -- unlike other backends. So turn this test for now.
      $ ([ "issue2362" ] <* guard (cg /= C))
      ++ ([ "popen2" ] <* guard (cg /= Node))
      ++ [ -- Evaluator
       "evaluator004",
       -- Unfortunately the behaviour of Double is platform dependent so the
       -- following test is turned off.
       -- "evaluator005",
       "basic048",
       "perf006"]

||| Totality checking, including positivity
idrisTestsTotality : IO TestPool
idrisTestsTotality = testsInDir "idris2/total" "Totality checking"

-- This will only work with an Idris compiled via Chez or Racket, but at
-- least for the moment we're not officially supporting self hosting any
-- other way. If we do, we'll need to have a way to disable these.
idrisTestsSchemeEval : IO TestPool
idrisTestsSchemeEval = testsInDir "idris2/schemeeval" "Scheme Evaluator"

idrisTestsReflection : IO TestPool
idrisTestsReflection = testsInDir "idris2/reflection" "Quotation and Reflection"

idrisTestsWith : IO TestPool
idrisTestsWith = testsInDir "idris2/with" "With abstraction"

idrisTestsOperators : IO TestPool
idrisTestsOperators = testsInDir "idris2/operators" "Operator and fixities"

idrisTestsIPKG : IO TestPool
idrisTestsIPKG = testsInDir "idris2/pkg" "Package and .ipkg files"

idrisTests : TestPool
idrisTests = MkTestPool "Misc" [] Nothing
       -- Documentation strings
      ["docs001", "docs002", "docs003", "docs004", "docs005",
       -- Eta equality
       "eta001",
       -- Modules and imports
       "import001", "import002", "import003", "import004", "import005", "import006",
       "import007", "import008", "import009",
       -- Implicit laziness, lazy evaluation
       "lazy001", "lazy002", "lazy003", "lazy004", "lazy005",
       -- Namespace blocks
       "namespace001", "namespace002", "namespace003", "namespace004", "namespace005",
       -- Parameters blocks
       "params001", "params002", "params003", "params004",
       -- Larger programs arising from real usage. Typically things with
       -- interesting interactions between features
       "real001", "real002",
       -- Inlining
       "inlining001",
       -- with-disambiguation
       "with003",
       -- pretty printing
       "pretty001", "pretty002",
       -- PrimIO
       "primloop",
       -- golden file testing
       "golden001",
       -- quantifiers
       "quantifiers001",
       -- unification
       "unification001"
       ]

typeddTests : IO TestPool
typeddTests = testsInDir "typedd-book" "Type Driven Development"

chezTests : IO TestPool
chezTests = testsInDir "chez" "Chez backend" {codegen = Just Chez}

refcTests : IO TestPool
refcTests = testsInDir "refc" "Reference counting C backend" {codegen = Just C}

racketTests : IO TestPool
racketTests = testsInDir "racket" "Racket backend" {codegen = Just Racket}
  { pred = not . (`elem` ["conditions006", "conditions007"]) }

nodeTests : IO TestPool
nodeTests = testsInDir "node" "Node backend" {codegen = Just Node}

vmcodeInterpTests : IO TestPool
vmcodeInterpTests = testsInDir "vmcode" "VMCode interpreter"

ideModeTests : IO TestPool
ideModeTests = testsInDir "ideMode" "IDE mode"

preludeTests : IO TestPool
preludeTests = testsInDir "prelude" "Prelude library"

templateTests : IO TestPool
templateTests = testsInDir "templates" "Test templates"

-- base library tests are run against
-- each codegen supported and to keep
-- things simple it's all one test group
-- that only runs if all backends are
-- available.
baseLibraryTests : IO TestPool
baseLibraryTests = testsInDir "base" "Base library" {requirements = [Chez, Node]}

-- same behavior as `baseLibraryTests`
contribLibraryTests : IO TestPool
contribLibraryTests = testsInDir "contrib" "Contrib library" {requirements = [Chez, Node]}

-- same behavior as `baseLibraryTests`
linearLibraryTests : IO TestPool
linearLibraryTests = testsInDir "linear" "Linear library" {requirements = [Chez, Node]}

codegenTests : IO TestPool
codegenTests = testsInDir "codegen" "Code generation"

main : IO ()
main = runner $
  [ !ttimpTests
  , !idrisTestsBasic
  , !idrisTestsCoverage
  , !idrisTestsTermination
  , !idrisTestsCasetree
  , !idrisTestsError
  , !idrisTestsFailing
  , !idrisTestsWarning
  , !idrisTestsInteractive
  , !idrisTestsInterface
  , !idrisTestsLiterate
  , !idrisTestsLinear
  , !idrisTestsPerformance
  , !idrisTestsRegression
  , !idrisTestsData
  , !idrisTestsBuiltin
  , !idrisTestsEvaluator
  , !idrisTestsREPL
  , !idrisTestsTotality
  , !idrisTestsSchemeEval
  , !idrisTestsReflection
  , !idrisTestsWith
  , !idrisTestsOperators
  , !idrisTestsDebug
  , !idrisTestsIPKG
  , testPaths "idris2/misc" idrisTests
  , !typeddTests
  , !ideModeTests
  , !preludeTests
  , !baseLibraryTests
  , !linearLibraryTests
  , !contribLibraryTests
  , !chezTests
  , !refcTests
  , !racketTests
  , !nodeTests
  , !vmcodeInterpTests
  , !templateTests
  , !codegenTests
  ]
  ++ !(traverse idrisTestsAllSchemes [Chez, Racket])
  ++ map (testPaths "allbackends" . idrisTestsAllBackends) [Chez, Node, Racket, C]


    where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
