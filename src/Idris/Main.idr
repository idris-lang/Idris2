module Idris.Main

import Idris.Driver
import Compiler.Common

main : IO ()
main = mainWithCodegens []
