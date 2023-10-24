module Inside.PrintDirs

import Language.Reflection

dirs : List (String, LookupDir)
dirs =
  [ ("project dir"       , ProjectDir      )
  , ("source dir"        , SourceDir       )
  , ("current module dir", CurrentModuleDir)
  , ("submodules dir"    , SubmodulesDir   )
  , ("build dir"         , BuildDir        )
  ]

logAllDirs : Elab ()
logAllDirs = for_ dirs $ \(msg, lk) => logMsg "elab" 0 "\{msg}: \{!(idrisDir lk)}"

%language ElabReflection

%runElab logAllDirs
