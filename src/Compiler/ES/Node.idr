||| The `Node` generator.
module Compiler.ES.Node

import Idris.Env
import Idris.Syntax

import Compiler.ES.Codegen

import Compiler.Common

import Libraries.Utils.Path

import System
import System.File.Permissions

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

||| Compile a TT expression to Node with source map
compileToNodeWithSourceMap :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm ->
  (outfile : String) ->
  Core (String, String)
compileToNodeWithSourceMap c s tm outfile = do
  (js, sourceMap) <- compileToESWithSourceMap c s Node tm ["node", "javascript"] outfile
  pure (shebang ++ js, sourceMap)
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
  do -- Check for sourcemap directive
     directives <- getDirectives Node
     let out = outputDir </> outfile
     if "sourcemap" `elem` directives
       then do
         (es, sourceMap) <- compileToNodeWithSourceMap c s tm outfile
         Core.writeFile out es
         Core.writeFile (out ++ ".map") sourceMap
         coreLift_ $ chmodRaw out 0o755
         pure (Just out)
       else do
         es <- compileToNode c s tm
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
     js <- compileToNode c s tm
     Core.writeFile outn js
     node <- coreLift findNode
     quoted_node <- pure $ "\"" ++ node ++ "\"" -- Windows often have a space in the path.
     coreLift_ $ system (quoted_node ++ " " ++ outn)

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr Nothing Nothing
