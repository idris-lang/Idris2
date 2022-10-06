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

import Data.Maybe

%default covering

findNode : IO String
findNode = do
   Nothing <- idrisGetEnv "NODE"
      | Just node => pure node
   path <- pathLookup ["node"]
   pure $ fromMaybe "/usr/bin/env node" path

||| Compile a TT expression to Node
compileToNode :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm -> Core String
compileToNode c s tm = compileToES c s Node tm ["node", "javascript"]

||| Node implementation of the `compileExpr` interface.
compileExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) ->
  (outputDir : String) ->
  ClosedTerm ->
  (outfile : String) ->
  Core (Maybe String)
compileExpr c s tmpDir outputDir tm outfile =
  do es <- compileToNode c s tm
     let out = outputDir </> outfile
     Core.writeFile out es
     pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm =
  do let outn = tmpDir </> "_tmp_node.js"
     js <- compileToNode c s tm
     Core.writeFile outn js
     node <- coreLift findNode
     quoted_node <- pure $ "\"" ++ node ++ "\"" -- Windows often have a space in the path.
     coreLift_ $ system (quoted_node ++ " " ++ outn)

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr Nothing Nothing
