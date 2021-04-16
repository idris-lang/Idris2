module Compiler.ES.Node

import Idris.Env

import Compiler.ES.ES

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.TT
import Libraries.Utils.Path

import System
import System.File

import Data.Maybe

findNode : IO String
findNode = do
   Nothing <- idrisGetEnv "NODE"
      | Just node => pure node
   path <- pathLookup ["node"]
   pure $ fromMaybe "/usr/bin/env node" path

||| Compile a TT expression to Node
compileToNode : Ref Ctxt Defs ->
              ClosedTerm -> Core String
compileToNode c tm = do
  compileToES c tm ["node", "javascript"]

||| Node implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile
    = do es <- compileToNode c tm
         let out = outputDir </> outfile
         Right () <- coreLift (writeFile out es)
            | Left err => throw (FileErr out err)
         pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm
= do let outn = tmpDir </> "_tmp_node" ++ ".js"
     js <- compileToNode c tm
     Right () <- coreLift $ writeFile outn js
        | Left err => throw (FileErr outn err)
     node <- coreLift findNode
     quoted_node <- pure $ "\"" ++ node ++ "\"" -- Windows often have a space in the path.
     coreLift_ $ system (quoted_node ++ " " ++ outn)
     pure ()

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr
