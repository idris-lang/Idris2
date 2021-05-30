module Main

import Libraries.Data.Version
import Compiler.Scheme.Chez

parseChezVersion : IO ()
parseChezVersion = do
  chez <- findChez
  version <- chezVersion chez
  print (version /= Nothing)
