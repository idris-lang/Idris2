||| Check that we cannot implement function illegally escaping zero quantity using elaboration reflection
module NoEscapePar

import Language.Reflection

%language ElabReflection

escScr : Elab $ (0 _ : a) -> a
escScr = check $ ILam EmptyFC M0 ExplicitArg (Just `{x}) `(a) `(x)

failing "x is not accessible in this context"

  esc : (0 _ : a) -> a
  esc = %runElab escScr

escd : (0 _ : a) -> a

0 escd' : (0 _ : a) -> a

escDecl : Name -> Elab Unit
escDecl name = declare [
                 IDef EmptyFC name [
                   PatClause EmptyFC
                     -- lhs
                     (IApp EmptyFC (IVar EmptyFC name) (IBindVar EmptyFC "x"))
                     -- rhs
                     `(x)
                 ]
               ]

%runElab escDecl `{escd'}

failing "x is not accessible in this context"

  %runElab escDecl `{escd}
