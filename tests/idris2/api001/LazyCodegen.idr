module Main

import Core.Context
import Compiler.Common
import Idris.Driver

compile : Ref Ctxt Defs -> (tmpDir : String) -> (execDir : String) ->
          ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs tmp dir term file = do coreLift $ putStrLn "I'd rather not."
                                    pure $ Nothing

execute : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
execute defs dir term = do coreLift $ putStrLn "Maybe in an hour."

lazyCodegen : Codegen
lazyCodegen = MkCG compile execute

main : IO ()
main = mainWithCodegens [("lazy", lazyCodegen)]
