module Broken

import Language.Reflection

%default total

%language ElabReflection

decls : List Decl
decls =
  let con = MN "MkVoidContainer" 0
   in [ IData EmptyFC (SpecifiedValue Export) Nothing $
              MkData EmptyFC `{ VoidContainer } (Just `( Type )) []
                     [ MkTy EmptyFC (NoFC con) `( Void -> VoidContainer ) ] ]

%runElab declare decls

export
Uninhabited VoidContainer
