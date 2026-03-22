||| The `Javascript` code generator.
module Compiler.ES.Javascript

import Compiler.ES.Codegen

import Compiler.Common

import Libraries.Utils.Path

import Idris.Env
import Idris.Syntax

import Data.String

%default covering

||| Compile a TT expression to Javascript
compileToJS :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm -> Core String
compileToJS c s tm = compileToES c s Javascript tm ["browser", "javascript"]

||| Compile a TT expression to Javascript with source map
compileToJSWithSourceMap :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  ClosedTerm ->
  (outfile : String) ->
  Core (String, String)
compileToJSWithSourceMap c s tm outfile =
  compileToESWithSourceMap c s Javascript tm ["browser", "javascript"] outfile

htmlHeader : String
htmlHeader = """
  <html>
    <head>
      <meta charset='utf-8'>
    </head>
    <body>
      <script type='text/javascript'>

  """

htmlFooter : String
htmlFooter = """

      </script>
    </body>
  </html>
  """

addHeaderAndFooter : String -> String -> String
addHeaderAndFooter outfile es =
  case toLower <$>  extension outfile of
    Just "html" => htmlHeader ++ es ++ htmlFooter
    _ => es

||| Javascript implementation of the `compileExpr` interface.
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
     directives <- getDirectives Javascript
     let out = outputDir </> outfile
     if "sourcemap" `elem` directives
       then do
         (es, sourceMap) <- compileToJSWithSourceMap c s tm outfile
         let res = addHeaderAndFooter outfile es
         Core.writeFile out res
         Core.writeFile (out ++ ".map") sourceMap
         pure (Just out)
       else do
         es <- compileToJS c s tm
         let res = addHeaderAndFooter outfile es
         Core.writeFile out res
         pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr :
  Ref Ctxt Defs ->
  Ref Syn SyntaxInfo ->
  (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm =
  throw $ InternalError "Javascript backend is only able to compile, use Node instead"

||| Codegen wrapper for Javascript implementation.
export
codegenJavascript : Codegen
codegenJavascript = MkCG compileExpr executeExpr Nothing Nothing
