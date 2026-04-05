module Main

import Idris.Package.Types
import Idris.Pretty
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

pkg : PkgDesc
pkg =
  { authors := Just "Tomáš"
  } (initPkgDesc "package")

main : IO ()
main = putStrLn $ renderString $ layoutUnbounded $ pretty pkg
