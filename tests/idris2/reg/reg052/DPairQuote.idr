module DPairQuote

import Language.Reflection

%default total
%language ElabReflection
%default total

extract : Type -> Elab Unit
extract ty = logTerm "debug.elab" 0 "type" !(quote ty)

%macro
extract' : Type -> Elab Unit
extract' = extract -- logTerm "debug.elab" 0 "type" !(quote ty)

data Y : Nat -> Type -> Type where
  Y0 : Y 0 Int
  Y1 : Y 1 Nat

X : Type
X = (n : Nat ** x : Type ** Y n x)

%runElab extract X

v : Unit
v = %runElab extract X

u : Unit
u = extract' X

%runElab extract (n : Nat ** x : Type ** Y n x)

v' : Unit
v' = %runElab extract (n : Nat ** x : Type ** Y n x)

u' : Unit
u' = extract' (n : Nat ** x : Type ** Y n x)
