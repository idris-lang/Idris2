module LessSimpleRW

import Language.Reflection

%default total

readAndLog : (path : String) -> Elab ()
readAndLog path = do
  v <- readFile CurrentModuleDir path
  logMsg "elab" 0 "reading \{path}:"
  logMsg "elab" 0 $ ("    " ++) $ maybe "FILE DOES NOT EXIST" ("contents:\n" ++) v

writeAndLog : (path : String) -> Elab ()
writeAndLog path = do
  writeFile CurrentModuleDir path "WRITTEN CONTENTS\nLA-LA-LA\n"
  logMsg "elab" 0 "written to \{path}"

%language ElabReflection

-- Check that we can write to a dir that was not previously existent
%runElab writeAndLog "nonExistentOriginally/a-generated-file"

-- Check that '..' in path are okay unless they escape the lookup dir
%runElab readAndLog "nonExistentOriginally/../nonExistentOriginally/a-generated-file"

-- Check double dots are allowed inside file names
%runElab writeAndLog "..a-dot-named-file"

failing "path must not escape the directory"

  -- Check that we cannot escape
  %runElab readAndLog "../whatever"

failing "path must not escape the directory"

  -- Check a slightly more complicated case of escaping
  %runElab readAndLog "nonExistentOriginally/../../whatever"
