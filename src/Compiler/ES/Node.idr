||| The `Node` generator.
module Compiler.ES.Node

import Idris.Env

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
compileToNode : Ref Ctxt Defs -> ClosedTerm -> Core String
compileToNode c tm = compileToES c Node tm ["node", "javascript"]

||| Node implementation of the `compileExpr` interface.
compileExpr :  Ref Ctxt Defs
            -> (tmpDir : String)
            -> (outputDir : String)
            -> ClosedTerm
            -> (outfile : String)
            -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile =
  do es <- compileToNode c tm
     let out = outputDir </> outfile
     Core.writeFile out es
     pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm =
  do let outn = tmpDir </> "_tmp_node.js"
     js <- compileToNode c tm
     Core.writeFile outn js
     node <- coreLift findNode
     quoted_node <- pure $ "\"" ++ node ++ "\"" -- Windows often have a space in the path.
     coreLift_ $ system (quoted_node ++ " " ++ outn)
     pure ()

||| Codegen wrapper for Node implementation.
export
codegenNode : Codegen
codegenNode = MkCG compileExpr executeExpr Nothing Nothing
