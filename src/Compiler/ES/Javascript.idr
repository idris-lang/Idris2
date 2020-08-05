module Compiler.ES.Javascript

import Compiler.ES.ES

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.TT
import Utils.Path

import System
import System.File

import Data.Maybe
import Data.Strings
import Data.String.Extra


||| Compile a TT expression to Javascript
compileToJS : Ref Ctxt Defs ->
              ClosedTerm -> Core String
compileToJS c tm = do
  compileToES c tm ["browser", "javascript"]

htmlHeader : String
htmlHeader = concat $ the (List String) $
           [ "<html>\n"
           , " <head>\n"
           , "  <meta charset='utf-8'>\n"
           , " </head>\n"
           , " <body>\n"
           , "  <script type='text/javascript'>\n"
           ]

htmlFooter : String
htmlFooter = concat $ the (List String) $
           [ "\n  </script>\n"
           , " </body>\n"
           , "</html>"
           ]

addHeaderAndFooter : String -> String -> String
addHeaderAndFooter outfile es =
  case toLower <$>  extension outfile of
    Just "html" => htmlHeader ++ es ++ htmlFooter
    _ => es

||| Javascript implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile
    = do es <- compileToJS c tm
         let res = addHeaderAndFooter outfile es
         let out = outputDir </> outfile
         Right () <- coreLift (writeFile out res)
            | Left err => throw (FileErr out err)
         pure (Just out)

||| Node implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm =
  throw $ InternalError "Javascript backend is only able to compile, use Node instead"

||| Codegen wrapper for Javascript implementation.
export
codegenJavascript : Codegen
codegenJavascript = MkCG compileExpr executeExpr
