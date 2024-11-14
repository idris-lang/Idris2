||| The `Javascript` code generator.
module Compiler.ES.Browser

import Compiler.ES.Codegen

import Compiler.Common
import Compiler.ES.State as Compiler.ES.State

import Core.Context
import Core.TT
import Core.Options
import Libraries.Utils.Path

import Idris.Syntax

import Data.String
import Debug.Trace

%default covering

||| Compile a TT expression to Javascript
compileToBrowserJS :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm ->
  (outputDir : String) ->
  Core String
compileToBrowserJS c s tm outputDir = compileToES c s BrowserJavascript tm Compiler.ES.State.BrowserPreferredJavascriptFallback outputDir

htmlHeader : String
htmlHeader = """
  <html>
    <head>
      <meta charset='utf-8'>
    </head>
    <body>
      <script type='module'>

  """

htmlFooter : String
htmlFooter = """

      </script>
    </body>
  </html>
  """

-- TODO (Maybe Html, JS)
addHeaderAndFooter : String -> String -> String
addHeaderAndFooter outfile es =
  case toLower <$> extension outfile of
    Just "html" => htmlHeader ++ es ++ htmlFooter
    _ => es

||| Browser implementation of the `compileExpr` interface.
compileBrowserExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) ->
  (outputDir : String) ->
  ClosedTerm ->
  (outfile : String) ->
  Core (Maybe String)
compileBrowserExpr c s tmpDir outputDir tm outfile =
  do es <- compileToBrowserJS c s tm outputDir
     let res = addHeaderAndFooter outfile es
     let out = outputDir </> outfile
     Core.writeFile out res
     pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeBrowserExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeBrowserExpr c s tmpDir tm =
  throw $ InternalError "Browser Javascript backend is only able to compile, use Node instead"

||| Codegen wrapper for Javascript implementation.
export
codegenBrowserJavascript : Codegen
codegenBrowserJavascript = MkCG compileBrowserExpr executeBrowserExpr Nothing Nothing
