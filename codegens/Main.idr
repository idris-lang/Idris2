module Main

import Compiler.Common
import Idris.Driver

import Scheme.Gambit

import ES.Javascript
import ES.Node

main : IO ()
main = mainWithCodegens [
     ("gambit", codegenGambit),
     ("node", codegenNode),
     ("javascript", codegenJavascript)
  ]
