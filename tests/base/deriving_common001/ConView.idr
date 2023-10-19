module ConView

import Data.Fin

import Deriving.Common

import Language.Reflection

%default total

%language ElabReflection

data X : Fin n -> Type where
  MkX1 : (fn : _) -> X fn
  MkX2 : (fn : Fin n) -> X {n} fn
  MkX3 : (fn : Fin n) -> X fn {n}

consParams : a -> Elab ()
consParams t = do
  t <- isType !(quote t)
  logMsg "elab" 0 "the type \{show t.typeConstructor}"
  for_ t.dataConstructors $ \(conName, conTy) => do
    let Just conView = constructorView conTy
      | Nothing => failAt (getFC conTy) "cannot intepret as a constructor"
    logMsg "elab" 0 "- constructor \{show conName}"
    for_ conView.params $ \(conParam, conIdx) => do
      logMsg "elab" 0 "  - param (arg #\{show conIdx}): \{show conParam}"

%runElab consParams X
