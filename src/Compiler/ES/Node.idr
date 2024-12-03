||| The `Node` generator.
module Compiler.ES.Node

import Idris.Env
import Idris.Syntax

import Compiler.ES.Codegen

import Compiler.Common

import Core.Context
import Core.Options
import Core.TT
import Libraries.Utils.Path

import System
import System.File.Permissions

import Data.Maybe

%default covering

envNode : String
envNode = "/usr/bin/env node"

findNode : IO String
findNode = do
   Nothing <- idrisGetEnv "NODE"
      | Just node => pure node
   path <- pathLookup ["node"]
   pure $ fromMaybe envNode path

||| Compile a TT expression to Node
compileToNode :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm -> Core String
compileToNode c s tm = do
  js <- compileToES c s Node tm ["node", "javascript"]
  pure $ shebang ++ js
  where
    shebang : String
    shebang = "#!\{envNode}\n"

||| Node implementation of the `compileExpr` interface.
compileExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) ->
  (outputDir : String) ->
  ClosedTerm ->
  (outfile : String) ->
  Core String
compileExpr c s tmpDir outputDir tm outfile =
  do es <- compileToNode c s tm
     let out = outputDir </> outfile
     writeFile out es
     handleFileError out $ chmodRaw out 0o755
     pure out

||| Node implementation of the `executeExpr` interface.
executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ExitCode
executeExpr c s tmpDir tm =
  do out <- compileExpr c s tmpDir tmpDir tm "_tmp_node.js"
     node <- coreLift findNode
     system [node, out]

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr Nothing Nothing
