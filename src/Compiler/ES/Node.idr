module Compiler.ES.Node

import Compiler.ES.ES

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.TT
import Utils.Path

import System
import System.File

import Data.Maybe

findNode : IO String
findNode =
  do env <- getEnv "NODE"
     pure $ fromMaybe "/usr/bin/env node" env

||| Compile a TT expression to Node
compileToNode : Ref Ctxt Defs ->
              ClosedTerm -> Core String
compileToNode c tm = do
  compileToES c tm

||| Node implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c execDir tm outfile
    = do es <- compileToNode c tm
         Right () <- coreLift (writeFile outfile es)
            | Left err => throw (FileErr outfile err)
         pure (Just outfile)

||| Node implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c execDir tm
= do let outn = execDir </> "_tmp_node" ++ ".js"
     js <- compileToNode c tm
     Right () <- coreLift $ writeFile outn js
        | Left err => throw (FileErr outn err)
     node <- coreLift findNode
     coreLift $ system (node ++ " " ++ outn)
     pure ()

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr
