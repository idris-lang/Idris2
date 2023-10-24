module UseMacroWithoutExtension

import DeclMacro

useMacro : Nat
useMacro = macroFun 5

useMacroCorr : UseMacroWithoutExtension.useMacro = 6
useMacroCorr = Refl

failing "%language ElabReflection not enabled"

  stillCan'tUseRunElabWithoutExtension : Nat
  stillCan'tUseRunElabWithoutExtension = %runElab justScript 4
