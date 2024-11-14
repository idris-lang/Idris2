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
import Compiler.ES.State as Compiler.ES.State
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
compileToNodeJS :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm ->
  (outputDir : String) ->
  Core String
compileToNodeJS c s tm outputDir = do
  js <- compileToES c s NodeJavascript tm Compiler.ES.State.NodePreferredJavascriptFallback outputDir
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
  Core (Maybe String)
compileExpr c s tmpDir outputDir tm outfile =
  do es <- compileToNodeJS c s tm outputDir
     let out = outputDir </> outfile
     Core.writeFile out es
     coreLift_ $ chmodRaw out 0o755
     pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm =
  do let outn = tmpDir </> "_tmp_node.js"
     js <- compileToNodeJS c s tm tmpDir
     Core.writeFile outn js
     node <- coreLift findNode
     quoted_node <- pure $ "\"" ++ node ++ "\"" -- Windows often have a space in the path.
     coreLift_ $ system (quoted_node ++ " " ++ outn)

||| Codegen wrapper for Node implementation.
export
codegenNodeJavascript : Codegen
codegenNodeJavascript = MkCG compileExpr executeExpr Nothing Nothing
