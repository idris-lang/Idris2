module RefDefs

import Language.Reflection

%default total

%language ElabReflection

simple : Nat -> Nat
simple x = x + 5

simpleRec : Nat -> Nat
simpleRec Z = 4
simpleRec (S n) = S $ simpleRec n

mutRec1 : Nat -> Nat
mutRec2 : Nat -> Nat

mutRec1 Z = Z
mutRec1 (S n) = mutRec2 n

mutRec2 Z = Z
mutRec2 (S n) = mutRec1 n

printRefDefs : Name -> Elab ()
printRefDefs name = do
  [(name, _)] <- getInfo name
    | [] => fail "definition \{show name} is not found"
    | ns@(_::_) => fail "name \{show name} is ambiguous: \{show $ fst <$> ns}"
  names <- getReferredFns name
  logMsg "elab" 0 "Names `\{show name}` refers to:"
  for_ names $ logMsg "elab" 0 . ("  - " ++) . show
  logMsg "elab" 0 ""

%runElab
  traverse_ printRefDefs
    [ `{RefDefs.simple}
    , `{RefDefs.simpleRec}
    , `{RefDefs.mutRec1}
    , `{Prelude.Bool}
    , `{Prelude.Nat}
    , `{Language.Reflection.TTImp.TTImp}
    ]
