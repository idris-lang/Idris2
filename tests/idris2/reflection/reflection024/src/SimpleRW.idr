module SimpleRW

import Language.Reflection

%default total

existentToRead, nonExistentToRead, existentToWrite, nonExistentToWrite : String
existentToRead     = "existentToRead"
nonExistentToRead  = "nonExistentToRead"
existentToWrite    = "existentToWrite"
nonExistentToWrite = "nonExistentToWrite"

readAndLog : (path : String) -> Elab ()
readAndLog path = do
  v <- readFile CurrentModuleDir path
  logMsg "elab" 0 "reading \{path}:"
  logMsg "elab" 0 $ ("    " ++) $ maybe "FILE DOES NOT EXIST" ("contents:\n" ++) v

writeAndLog : (path : String) -> Elab ()
writeAndLog path = do
  writeFile CurrentModuleDir path "WRITTEN CONTENTS\nLA-LA-LA\n"
  logMsg "elab" 0 "written to \{path}"

go : Elab ()
go = do
  readAndLog existentToRead
  readAndLog nonExistentToRead
  writeAndLog existentToWrite
  writeAndLog nonExistentToWrite

%language ElabReflection

%runElab go
