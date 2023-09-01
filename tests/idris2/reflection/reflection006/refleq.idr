import Language.Reflection

%language ElabReflection

solveReflected : TTImp -> Elab any
solveReflected `(Builtin.Equal {a=_} {b=_} ~(left) ~(right))
    = do logTerm "" 0 "Left" left
         logTerm "" 0 "Right" right
         fail "Not done"
solveReflected g
    = do logTerm "" 0 "Goal" g
         fail "I don't know how to prove this"

%macro
prove : Elab any
prove
    = do env <- localVars
         Just g <- goal
              | Nothing => fail "No goal to solve"
         logMsg "" 0 (show env)
         solveReflected g

commutes : (x, y : Nat) -> plus x y = plus y x
commutes x y = prove
