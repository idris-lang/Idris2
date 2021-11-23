||| The `Javascript` code generator.
module Compiler.ES.Javascript

import Compiler.ES.Codegen

import Compiler.Common

import Core.Context
import Core.TT
import Core.Options
import Libraries.Utils.Path

import Data.String

%default covering

||| Compile a TT expression to Javascript
compileToJS : Ref Ctxt Defs ->
              ClosedTerm -> Core String
compileToJS c tm = compileToES c Javascript tm ["browser", "javascript"]

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
compileExpr :  Ref Ctxt Defs
            -> (tmpDir : String)
            -> (outputDir : String)
            -> ClosedTerm
            -> (outfile : String)
            -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile =
  do es <- compileToJS c tm
     let res = addHeaderAndFooter outfile es
     let out = outputDir </> outfile
     Core.writeFile out res
     pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm =
  throw $ InternalError "Javascript backend is only able to compile, use Node instead"

||| Codegen wrapper for Javascript implementation.
export
codegenJavascript : Codegen
codegenJavascript = MkCG compileExpr executeExpr Nothing Nothing
