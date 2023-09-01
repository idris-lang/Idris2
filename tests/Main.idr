module Main

import System
import System.Directory
import System.File

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

ttimpTests : IO TestPool
ttimpTests = testsInDir "ttimp" (const True) "TTImp" [] Nothing

idrisTestsBasic : IO TestPool
idrisTestsBasic = testsInDir "idris2/basic" (const True) "Fundamental language features" [] Nothing

idrisTestsDebug : IO TestPool
idrisTestsDebug = testsInDir "idris2/debug" (const True) "Debug features" [] Nothing

idrisTestsCoverage : IO TestPool
idrisTestsCoverage = testsInDir "idris2/coverage" (const True) "Coverage checking" [] Nothing

idrisTestsTermination : IO TestPool
idrisTestsTermination = testsInDir "idris2/termination" (const True) "Termination checking" [] Nothing

idrisTestsCasetree : IO TestPool
idrisTestsCasetree = testsInDir "idris2/casetree" (const True) "Case tree building" [] Nothing

idrisTestsWarning : IO TestPool
idrisTestsWarning = testsInDir "idris2/warning" (const True) "Warnings" [] Nothing

idrisTestsFailing : IO TestPool
idrisTestsFailing = testsInDir "idris2/failing" (const True) "Failing blocks" [] Nothing

||| Error messages, including parse errors ("perror")
idrisTestsError : IO TestPool
idrisTestsError = testsInDir "idris2/error" (const True) "Error messages" [] Nothing

idrisTestsInteractive : IO TestPool
idrisTestsInteractive = testsInDir "idris2/interactive" (const True) "Interactive editing" [] Nothing

idrisTestsInterface : IO TestPool
idrisTestsInterface = testsInDir "idris2/interface" (const True) "Interface" [] Nothing

||| QTT and linearity related
idrisTestsLinear : IO TestPool
idrisTestsLinear = testsInDir "idris2/linear" (const True) "Quantities" [] Nothing

idrisTestsLiterate : IO TestPool
idrisTestsLiterate = testsInDir "idris2/literate" (const True) "Literate programming" [] Nothing

||| Performance: things which have been slow in the past, or which
||| pose interesting challenges for the elaborator
idrisTestsPerformance : IO TestPool
idrisTestsPerformance = testsInDir "idris2/perf" (const True) "Performance" [] Nothing

idrisTestsRegression : IO TestPool
idrisTestsRegression = testsInDir "idris2/reg" (const True) "Various regressions" [] Nothing

||| Data types, including records
idrisTestsData : IO TestPool
idrisTestsData = testsInDir "idris2/data" (const True) "Data and record types" [] Nothing

||| %builtin related tests for the frontend (type-checking)
idrisTestsBuiltin : IO TestPool
idrisTestsBuiltin = testsInDir "idris2/builtin" (const True) "Builtin types and functions" [] Nothing

||| Evaluator, REPL, specialisation
idrisTestsEvaluator : IO TestPool
idrisTestsEvaluator = testsInDir "idris2/evaluator" (const True) "Evaluation" [] Nothing

idrisTestsREPL : IO TestPool
idrisTestsREPL = testsInDir "idris2/repl" (const True) "REPL commands and help" [] Nothing

idrisTestsAllSchemes : Requirement -> IO TestPool
idrisTestsAllSchemes cg = testsInDir "allschemes" (const True)
      ("Test across all scheme backends: " ++ show cg ++ " instance")
      [] (Just cg)

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
idrisTestsTotality = testsInDir "idris2/total" (const True) "Totality checking" [] Nothing

-- This will only work with an Idris compiled via Chez or Racket, but at
-- least for the moment we're not officially supporting self hosting any
-- other way. If we do, we'll need to have a way to disable these.
idrisTestsSchemeEval : IO TestPool
idrisTestsSchemeEval = testsInDir "idris2/schemeeval" (const True) "Scheme Evaluator" [] Nothing

idrisTestsReflection : IO TestPool
idrisTestsReflection = testsInDir "idris2/reflection" (const True) "Quotation and Reflection" [] Nothing

idrisTestsWith : IO TestPool
idrisTestsWith = testsInDir "idris2/with" (const True) "With abstraction" [] Nothing

idrisTestsIPKG : IO TestPool
idrisTestsIPKG = testsInDir "idris2/pkg" (const True) "Package and .ipkg files" [] Nothing

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
       "lazy001", "lazy002", "lazy003",
       -- Namespace blocks
       "namespace001", "namespace002", "namespace003", "namespace004", "namespace005",
       -- Parameters blocks
       "params001", "params002", "params003",
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
typeddTests = testsInDir "typedd-book" (const True) "Type Driven Development" [] Nothing

chezTests : IO TestPool
chezTests = testsInDir "chez" (const True) "Chez backend" [] (Just Chez)

refcTests : IO TestPool
refcTests = testsInDir "refc" (const True) "Reference counting C backend" [] (Just C)

racketTests : IO TestPool
racketTests = testsInDir "racket" (const True) "Racket backend" [] (Just Racket)

nodeTests : IO TestPool
nodeTests = testsInDir "node" (const True) "Node backend" [] (Just Node)

vmcodeInterpTests : IO TestPool
vmcodeInterpTests = testsInDir "vmcode" (const True) "VMCode interpreter" [] Nothing

ideModeTests : IO TestPool
ideModeTests = testsInDir "ideMode" (const True) "IDE mode" [] Nothing

preludeTests : IO TestPool
preludeTests = testsInDir "prelude" (const True) "Prelude library" [] Nothing

templateTests : IO TestPool
templateTests = testsInDir "templates" (const True) "Test templates" [] Nothing

-- base library tests are run against
-- each codegen supported and to keep
-- things simple it's all one test group
-- that only runs if all backends are
-- available.
baseLibraryTests : IO TestPool
baseLibraryTests = testsInDir "base" (const True) "Base library" [Chez, Node] Nothing

-- same behavior as `baseLibraryTests`
contribLibraryTests : IO TestPool
contribLibraryTests = testsInDir "contrib" (const True) "Contrib library" [Chez, Node] Nothing

codegenTests : IO TestPool
codegenTests = testsInDir "codegen" (const True) "Code generation" [] Nothing

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
  , !idrisTestsDebug
  , !idrisTestsIPKG
  , testPaths "idris2/misc" idrisTests
  , !typeddTests
  , !ideModeTests
  , !preludeTests
  , !baseLibraryTests
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
