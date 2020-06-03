module Compiler.ES.Node

import Compiler.ES.ES

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.TT

import System
import System.File

%default partial

||| Compile a TT expression to Node
compileToNode : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core ()
compileToNode c tm outfile = do
  es <- compileToES c tm
  coreLift (writeFile outfile es)
  pure ()

||| Node implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c execDir tm outfile
    = do compileToNode c tm outfile
         pure (Just outfile)

||| Node implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c execDir tm
    = do coreLift $ system "!!!no execute for node yet!!!!"
         pure ()

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr
