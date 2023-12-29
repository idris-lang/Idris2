module CurrFn

import Language.Reflection

%default total

%language ElabReflection

logCurrFn : Elab ()
logCurrFn = logMsg "elab" 0 "current fn: \{show !getCurrentFn}"

%runElab logCurrFn

f : Nat -> Nat
f x = case %runElab logCurrFn of () => x + 4

f' : Nat -> Nat
f' x = x + case %runElab logCurrFn of () => 4

f'' : Nat -> Nat
f'' Z     = 4
f'' (S x) = f $ case %runElab logCurrFn of () => x

f''' : Nat -> Nat
f''' x = case x of
           Z   => 4
           S x => f $ case %runElab logCurrFn of () => x

n : Nat -> Nat
n x = x + f x where
  f : Nat -> Nat
  f x = case %runElab logCurrFn of () => x + 4

w : Nat -> Nat
w x with (x + 5)
  _ | Z   = x + case %runElab logCurrFn of () => 4
  _ | S n = f $ case %runElab logCurrFn of () => n
