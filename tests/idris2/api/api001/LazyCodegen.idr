||| NOTE: Please keep this file in sync with the example in docs/source/backends/custom.rst

module Main

import Core.Context
import Compiler.Common
import Idris.Driver
import Idris.Syntax
import System

compile :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> (execDir : String) ->
  ClosedTerm -> (outfile : String) -> Core String
compile defs syn tmp dir term file
  = do coreLift $ putStrLn "I'd rather not."
       throw $ InternalError "Compile is not implemented"

execute :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (execDir : String) -> ClosedTerm -> Core ExitCode
execute defs syn dir term
  = do coreLift $ putStrLn "Maybe in an hour."
       pure ExitSuccess

lazyCodegen : Codegen
lazyCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("lazy", lazyCodegen)]
