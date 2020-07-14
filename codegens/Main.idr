module Main

import Data.List

import Idris.Driver

import Compiler.Common

import Scheme.Chez
import Scheme.Racket
import Scheme.Gambit

import ES.Javascript
import ES.Node

main : IO ()
main = mainWithCodegens [
     ("chez", codegenChez)
   , ("racket", codegenRacket)
   , ("gambit", codegenGambit)
   , ("node", codegenNode)
   , ("javascript", codegenJavascript)
  ]
